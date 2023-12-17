`include "util.vh"
`include "const.vh"

module cache #
(
    parameter LINES = 64,
    parameter CPU_WIDTH = `CPU_INST_BITS, //32
    parameter WORD_ADDR_BITS = `CPU_ADDR_BITS-`ceilLog2(`CPU_INST_BITS/8) //32 - log2(32/8) = 30
)
(
    input clk,
    input reset,

    input                       cpu_req_valid,
    output reg                  cpu_req_ready,
    input [WORD_ADDR_BITS-1:0]  cpu_req_addr,
    input [CPU_WIDTH-1:0]       cpu_req_data,
    input [3:0]                 cpu_req_write,

    output reg                  cpu_resp_valid,
    output  [CPU_WIDTH-1:0]  cpu_resp_data,

    output reg                  mem_req_valid,
    input                       mem_req_ready,
    output reg [WORD_ADDR_BITS-1:`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)] mem_req_addr,
    output reg                       mem_req_rw,
    output reg                       mem_req_data_valid,
    input                            mem_req_data_ready,
    output reg [`MEM_DATA_BITS-1:0]  mem_req_data_bits,
    // byte level masking
    output reg [(`MEM_DATA_BITS/8)-1:0]  mem_req_data_mask,

    input                       mem_resp_valid,
    input [`MEM_DATA_BITS-1:0]  mem_resp_data
);

    //===== Parameter Declaration =====

    // Cache parameters
    parameter SIZE  = 4096*8; // 512*64
    parameter NWAYS = 1;
    parameter NSETS = LINES/NWAYS; // 64/1=64

    // Memory related paramter
    parameter MWIDTH = 128;

    // Cache T/I/O
    parameter INDEX_WIDTH  = `ceilLog2(NSETS); // ceilLog2(64) = 6
    parameter BLOCK_OFFSET = 4; // ceilLog2(512/32)
    parameter TAG_WIDTH    = WORD_ADDR_BITS - INDEX_WIDTH - BLOCK_OFFSET; // 30 - 6 - 4 = 20
    parameter VALIDBIT	   = 1;
    parameter DIRTYBIT     = 1;

    // State
    parameter   IDLE        = 4'd0;
    parameter	READ_C		= 4'd1;
    parameter	OUTPUT		= 4'd10;
    parameter	WRITE_C		= 4'd2;

    parameter	READ_M		= 4'd3;
    parameter	WAIT_4_M	= 4'd4;
    parameter	UPDATE_C	= 4'd5;

    parameter	CHECK_C	    = 4'd6;
    parameter	WAIT_4_C	= 4'd7;
    parameter	UPDATE_M	= 4'd8;
    parameter	BUFF_0	    = 4'd9;
    parameter	BUFF_1	    = 4'd11;

    //===== Reg/Wire Declaration =====
    
    reg     [1:0] count;
    reg     flag;
    reg     [1:0] cnt_hit;

    // state
    reg     [3:0] state;

    // SRAM for data and meta
    wire	[CPU_WIDTH-1:0] data_0;	// 32-bit
    wire	[CPU_WIDTH-1:0] data_1;    
    wire	[CPU_WIDTH-1:0] data_2;
    wire	[CPU_WIDTH-1:0] data_3;

    wire	[(CPU_WIDTH)-1:0] rdata;
    reg	    [(CPU_WIDTH)-1:0] wdata;
    reg	    [(CPU_WIDTH)-1:0] wdata_0, wdata_1, wdata_2, wdata_3;
    reg     [3:0] wmask;
    reg     [3:0] wmask_wr;

    // wire    [(VALIDBIT+DIRTYBIT+TAG_WIDTH-1):0]	rtag; // 22-bit
    // reg	    [(VALIDBIT+DIRTYBIT+TAG_WIDTH-1):0] wtag;
    wire    [(CPU_WIDTH-1):0] rtag; // 22-bit
    reg	    [(CPU_WIDTH-1):0] wtag;
    
    // Write Enable
    reg	data_we_0;	
    reg	data_we_1;	
    reg	data_we_2;	
    reg	data_we_3;	
    reg	meta_we;	
    
    // address
    reg     [WORD_ADDR_BITS-1:0]  addr_next; // 30-bit

    // T/I/O
    wire	[     TAG_WIDTH-1:0]	    tag; // 20-bit
    wire	[   INDEX_WIDTH-1:0]	  index; //  6-bit -- 64
    reg 	[   INDEX_WIDTH+1:0] data_index; //  8-bit -- 256
    wire	[  BLOCK_OFFSET-1:0]   	 blksel; //  4-bit
    wire	[     INDEX_WIDTH:0]index_plus1; //  7-bit

    // Meta
    wire   valid;
    wire   dirty;

    // Hit
    wire   hit;

    assign tag        = (state == IDLE) ? cpu_req_addr[WORD_ADDR_BITS-1:WORD_ADDR_BITS-TAG_WIDTH] : addr_next[WORD_ADDR_BITS-1:WORD_ADDR_BITS-TAG_WIDTH];
    assign index      = (state == IDLE) ? cpu_req_addr[WORD_ADDR_BITS-TAG_WIDTH-1:BLOCK_OFFSET]   : addr_next[WORD_ADDR_BITS-TAG_WIDTH-1:BLOCK_OFFSET];
    assign blksel     = (state == IDLE) ? cpu_req_addr[BLOCK_OFFSET-1:0]                          : addr_next[BLOCK_OFFSET-1:0];
    assign index_plus1= index + 1;
    //assign data_index = ({{2{1'b0}},index} << 2) + {{4{1'b0}},blksel[3:2]};

    assign valid = rtag[21];

    assign dirty = rtag[20];

    assign hit = valid & (tag == rtag[TAG_WIDTH-1:0]);

    assign cpu_resp_data = (cpu_req_addr[3:0] == 4'd0 && state != READ_C) ? `INSTR_NOP : (blksel[1:0] == 2'd0) ? data_0 :
                   (blksel[1:0] == 2'd1) ? data_1 :
                   (blksel[1:0] == 2'd2) ? data_2 : data_3;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state          <=  READ_C;
            wdata          <= 32'd0;
            wtag           <= 22'd0;
            flag           <=  1'b0;

            addr_next      <= cpu_req_addr;
            count          <=  2'd0;
            cnt_hit        <=  2'd0;
            data_index     <= ({{2{1'b0}},index} << 2) + {{6{1'b0}},blksel[3:2]};

            cpu_req_ready  <=  1'b0;
            cpu_resp_valid <=  1'b0;
            mem_req_valid  <=  1'b0;

            mem_req_addr       <= cpu_req_addr[WORD_ADDR_BITS-1 :`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)];
            mem_req_data_valid <=   1'b0;
            mem_req_data_bits  <= 128'd0;
            mem_req_data_mask  <= 16'hffff;
            mem_req_rw         <=  1'b0;

            data_we_0      <=  1'b0;
            data_we_1      <=  1'b0;
            data_we_2      <=  1'b0;
            data_we_3      <=  1'b0;
            meta_we        <=  1'b0;
        end
        else begin
            case(state)
                IDLE: begin
                    addr_next      <= cpu_req_addr;
                    data_index     <= ({{2{1'b0}},index} << 2) + {{6{1'b0}},blksel[3:2]};
                    count          <=  2'd0;
                    cpu_resp_valid <=  1'b0;
                    mem_req_valid  <=  1'b0;
                    cnt_hit        <=  2'd0;
                    wmask_wr       <= cpu_req_write;
                    if(cpu_req_addr[3:0] == 4'hf)
                        flag           <=  1'b0;
                    if(cpu_req_valid && cpu_req_ready && |cpu_req_write) begin // write cache
                        state          <= WRITE_C;
                        cpu_req_ready  <= 1'b0;
                        wdata          <= cpu_req_data;
                    end
                    else if(cpu_req_valid && cpu_req_ready) begin // read cache
                        state          <= READ_C;
                        cpu_req_ready  <= 1'b0;
                        wdata          <= 32'd0;
                    end
                    else begin // other
                        state          <= IDLE;
                        cpu_req_ready  <= 1'b1;
                        wdata          <= wdata;
                    end
                end
                READ_C: begin
                    cpu_req_ready  <= 1'b0;
                    if(addr_next[1:0] == 2'b11 && data_index[1:0] != 2'b11)
                        data_index     <= ({{2{1'b0}},index} << 2) + {{4{1'b0}},blksel[3:2]} +1;
                    
                    if(hit) // data in cache
                    begin
                        state          <= OUTPUT;
                        //cpu_req_ready  <= 1'b1;
                        cpu_resp_valid <= 1'b1;
                        //cpu_resp_data  <= rdata;
                    end
                    else // data not in cache
                    begin
                        mem_req_valid <= 1'b1;
                        mem_req_addr <= addr_next[WORD_ADDR_BITS-1 :`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)];
                        if(mem_req_ready)
                        begin
                            if(valid & dirty) // if dirty, first update Memory
                                state <= CHECK_C;
                            else              // read memory
                                state <= READ_M;
                        end
                        else
                            state <= state;
                    end
                end
                OUTPUT: begin
                    cpu_resp_valid <= 1'b0;
                    if(cpu_req_addr[3:0] == 4'd0 && ~flag && cnt_hit<2) begin
                        state          <= BUFF_1;
                        cpu_req_ready  <= 1'b0;
                        if(hit)
                            cnt_hit <= cnt_hit +1;
                    end
                    else if(cpu_req_addr[3:0] == 4'd0 && ~flag) begin
                        state          <= READ_C;
                        cpu_req_ready  <= 1'b1;
                    end
                    else begin
                        state          <= IDLE;
                        cpu_req_ready  <= 1'b1;
                    end
                end
                BUFF_1: begin
                    state          <= READ_C;
                    cpu_req_ready  <= 1'b0;
                    addr_next      <= cpu_req_addr;
                    data_index     <= ({{2{1'b0}},index} << 2) + {{6{1'b0}},blksel[3:2]};
                    count          <=  2'd0;
                    cpu_resp_valid <=  1'b0;
                    mem_req_valid  <=  1'b0;
                end
                WRITE_C: begin
                    if(hit) // data in cache
                    begin
                        state          <= IDLE;
                        cpu_req_ready  <= 1'd1;
                        cpu_resp_valid <= 1'b1;

                        meta_we        <= 1'd1;
                        wtag           <= {{10{1'b0}}, rtag[21], 1'b1, rtag[19:0]};
                        wmask          <= wmask_wr;

                        case(blksel[1:0])
                            2'd0: data_we_0 <= 1'b1;
                            2'd1: data_we_1 <= 1'b1;
                            2'd2: data_we_2 <= 1'b1;
                            2'd3: data_we_3 <= 1'b1;
                        endcase
                    end
                    else // data not in cache
                    begin
                        mem_req_valid <= 1'b1;
                        if(mem_req_ready) begin
                            if(valid & dirty) // if dirty, first update Memory
                                state <= CHECK_C;
                            else              // read memory
                                state <= READ_M;
                        end
                        else
                            state <= state;
                    end
                end
                READ_M: begin // read 4 times (128 bits a time, fill 512 bits cahce line)
                    //mem_req_addr <= addr_next[WORD_ADDR_BITS-1 :`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)] + count;
                        if(mem_req_ready && mem_req_valid)
                        begin
                            mem_req_rw    <= 1'd0;
                            state         <= WAIT_4_M;
                        end
                        else
                        begin
                            mem_req_rw <= 1'd0;
                            state  <= state;
                        end
                end
                WAIT_4_M: begin // wait for memory data
                    if(mem_resp_valid)
                    begin
                        data_index    <=  ({{2{1'b0}},index} << 2) + count;
                        data_we_0     <=  1'b1;
                        data_we_1     <=  1'b1;
                        data_we_2     <=  1'b1;
                        data_we_3     <=  1'b1;
                        wdata_0       <=  mem_resp_data[ 31: 0];
                        wdata_1       <=  mem_resp_data[ 63:32];
                        wdata_2       <=  mem_resp_data[ 95:64];
                        wdata_3       <=  mem_resp_data[127:96];
                        wmask         <=  4'b1111;
                        if(count == 3) begin
                            count     <=  0;
                            state     <=  UPDATE_C;
                            meta_we   <=  1'b0;
                            wtag      <=  {{10{1'b0}}, 1'b1, 1'b0, tag};
                        end
                        else begin
                            count     <=  count +1;
                            state     <=  state;
                            meta_we   <=  1'b1;
                            wtag      <=  {{10{1'b0}}, 1'b1, 1'b0, tag};
                        end
                    end
                    else
                    begin
                        state <= state;
                    end
                end
                UPDATE_C: begin // write cache 4 times and return to read cache
                    count         <=  2'd0;
                    data_we_0     <=  1'b0;
                    data_we_1     <=  1'b0;
                    data_we_2     <=  1'b0;
                    data_we_3     <=  1'b0;
                    state         <=  BUFF_0;
                    mem_req_addr  <= addr_next[WORD_ADDR_BITS-1 :`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)] + count;

                    data_index    <= ({{2{1'b0}},index} << 2) + {{4{1'b0}},blksel[3:2]};
                end
                BUFF_0: begin
                    state          <= READ_C;
                    cpu_req_ready  <= 1'b1;
                    if(addr_next == 30'h0000_0800)
                        flag           <= 1'b0;
                    else flag <= 1'b1;
                end
                CHECK_C: begin // check 4 times (total 512 bits, writh in memory 128 bits a time)
                    data_index    <=  {{2{1'b0}}, index} + count;
                    mem_req_addr  <= addr_next[WORD_ADDR_BITS-1 :`ceilLog2(`MEM_DATA_BITS/CPU_WIDTH)] + count;
                    if(mem_req_ready && mem_req_valid) begin
                        mem_req_rw    <= 1'd1;
                        state         <= WAIT_4_C;
                    end
                    else begin
                        mem_req_rw <= 1'd0;
                        state      <= state;
                    end
                end
                WAIT_4_C: begin // wait for cache data
                    state               <=  UPDATE_M;
                    mem_req_data_valid  <=  1'b1;
                    mem_req_data_mask   <=  16'hffff;
                    mem_req_data_bits   <=  {data_3, data_2, data_1, data_0};
                end
                UPDATE_M: begin // write cache 4 times and return to read cache
                    if(mem_req_data_valid && mem_req_data_ready)begin
                        if(count == 3) begin
                            state         <=  READ_M;
                            count         <=  2'd0;
                        end
                        else begin
                            count         <=  count + 1;
                            state         <=  CHECK_C;
                        end
                    end
                end
            endcase
        end
    end

    sram22_256x32m4w8 s0 (
    .clk(clk),
    .we(data_we_0),
    .wmask(wmask),
    .addr(data_index),
    .din(wdata_0),
    .dout(data_0));
    sram22_256x32m4w8 s1 (
    .clk(clk),
    .we(data_we_1),
    .wmask(wmask),
    .addr(data_index),
    .din(wdata_1),
    .dout(data_1));
    sram22_256x32m4w8 s2 (
    .clk(clk),
    .we(data_we_2),
    .wmask(wmask),
    .addr(data_index),
    .din(wdata_2),
    .dout(data_2));
    sram22_256x32m4w8 s3 (
    .clk(clk),
    .we(data_we_3),
    .wmask(wmask),
    .addr(data_index),
    .din(wdata_3),
    .dout(data_3));
    sram22_64x32m4w8 s4 (
    .clk(clk),
    .we(meta_we),
    .wmask(wmask),
    .addr(index),
    .din(wtag),
    .dout(rtag));

endmodule
