`include "const.vh"

// Editor: Evan Lin, Justine Tsai

module Riscv151(
    input clk,
    input reset,

    // Memory system ports
    output [31:0] dcache_addr,
    output reg [31:0] icache_addr,
    output [3:0] dcache_we,
    output dcache_re,
    output icache_re,
    output [31:0] dcache_din,
    input [31:0] dcache_dout,
    input [31:0] icache_dout,
    input stall, // if stall r <= w
    output reg [31:0] csr
);

    //===== Reg/Wire Declaration =====

    // MEM
    reg    [31:0] dcache_dout_ext;

    // PC
    reg    [31:0] PC          ;
    wire   [31:0] PC_plus4    ;  // PC+4
    reg    [31:0] ex_PC       ;
    reg    [31:0] ex_PC_plus4 ;
    reg    [31:0] wb_PC_plus4 ;
    reg           PC_start    ;

    // RegFile
    wire   [ 4:0] rs1, rs2, rd;
    wire   [31:0] rs1_data    ;
    wire   [31:0] rs2_data    ;
    wire   [31:0] rd_data     ;
    reg    [ 4:0] ex_rs1, ex_rs2;
    reg    [ 4:0] ex_rd, wb_rd;
    reg    [31:0] ex_rs1_data ;
    reg    [31:0] ex_rs2_data ;
    
    // ImmediateGeneration
    wire   [31:0] Immediate   ;    // immediate expansion
    reg    [31:0] ex_icache_dout;
    
    // ALU
    wire   [6:0]  opcode      ;
    wire   [2:0]  funct       ;
    wire          add_rshift_type;
    wire   [3:0]  ALUop       ;
    wire   [31:0] A, B        ;
    wire   [31:0] ALUout      ;
    reg    [31:0] wb_ALUout   ;
    reg    [2:0]  wb_funct    ;
    
    // Control
    wire       Asel, Bsel, Branch, MemRead            ;
    wire       MemtoReg, MemWrite, regWrite, Jump, CSR;
    reg        ex_Asel, ex_Bsel, ex_Branch, wb_Branch ;
    reg        ex_MemRead, ex_MemtoReg, wb_MemtoReg   ;
    reg        ex_MemWrite;
    reg        ex_regWrite, wb_regWrite               ;
    reg        ex_Jump, wb_Jump                       ;

    // Branch_comp
    wire   [31:0] Branch_A, Branch_B;
    wire          taken             ;

    // Forward
    wire       fw_wb2ex_A, fw_wb2ex_B;

    // Regfile
    Regfile I0(                           
        .clk(clk),                           
        .reset(reset),                       
        .wen(wb_regWrite),                      
        .a1(rs1),                            
        .a2(rs2),                            
        .aw(wb_rd),                             
        .d(rd_data),                         
        .q1(rs1_data),                       
        .q2(rs2_data)); 

    // ALU
    ALUdec I1(
        .opcode(opcode),
        .funct(funct),
        .add_rshift_type(add_rshift_type),
        .ALUop(ALUop));

    ALU I2( 
        .A(A),
        .B(B),
        .ALUop(ALUop),
        .Out(ALUout));
    
    // Immediate Generation
    ImmGen I3(
        .in_imm(ex_icache_dout),
        .out_imm(Immediate));

    // Control
    Control I4(
        .OpCode(icache_dout[6:0]),
        .Func(icache_dout[14:12]), 
        .Branch_w(Branch),
        .MemRead_w(MemRead), 
        .MemtoReg_w(MemtoReg),	
        .MemWrite_w(MemWrite),
        .RegWrite_w(regWrite),
        .Asel_w(Asel), 
        .Bsel_w(Bsel),
        .Jump_w(Jump),
        .CSR_w(CSR));

    // Branch_comp
    Branch_comp I5(
        .A(Branch_A),
        .B(Branch_B),
        .func3(funct),
        .taken(taken));

    // Load_ext
    Load_extention I6(
        .func3(wb_funct),
        .dcache_dout(dcache_dout),
        .wb_dcache_addr(wb_ALUout),
        .dcache_dout_ld_ext(dcache_dout_ext));

    // Assignment: RegFile
    assign  rs1 = icache_dout[19:15];
    assign  rs2 = icache_dout[24:20];
    assign  rd  = icache_dout[11:7];
    assign  rd_data = (wb_Jump)? wb_PC_plus4: ((wb_MemtoReg)? dcache_dout_ext: wb_ALUout);

    //Assignment: ALU
    assign  opcode = ex_icache_dout[6:0];
    assign  funct = ex_icache_dout[14:12];
    assign  add_rshift_type = ex_icache_dout[30];
    assign  fw_wb2ex_A = (wb_rd == 5'd0 && ex_rs1 == 5'd0) ? 1'b0 : (wb_rd == ex_rs1);
    assign  fw_wb2ex_B = ( (ex_icache_dout[6:0] == 7'b0010011) || (wb_rd == 5'd0 && ex_rs2 == 5'd0) ) ? 1'b0 : (wb_rd == ex_rs2);
    assign  A = ex_Asel ? ex_PC : fw_wb2ex_A ? rd_data : ex_rs1_data;
    assign  B = ex_Bsel ? Immediate : fw_wb2ex_B ? rd_data : ex_rs2_data;
    assign  Branch_A = fw_wb2ex_A ? rd_data : ex_rs1_data;
    assign  Branch_B = fw_wb2ex_B ? rd_data : ex_rs2_data;

    // Assignment: PC
    assign  PC_plus4 = PC + 32'd4;

    // Assignment: Memory
    assign  dcache_addr = ALUout;
    assign  icache_re = ~stall;
    assign  dcache_re = ~stall & ex_MemRead;
    assign  dcache_we = ex_MemWrite ? 
                        (funct == 3'b010) ? 4'b1111 : 
                        (funct == 3'b001) ? (4'b0011 << (dcache_addr[1:0])) :
                        (funct == 3'b000) ? (4'b0001 << (dcache_addr[1:0])) : 4'd0 : 4'd0 ;
    assign  dcache_din = (wb_rd == ex_rs2 && ex_rs2 != 5'd0) ? 
                         (rd_data<< ({{30{1'b0}},dcache_addr[1:0]}<<3)) : 
                         (ex_rs2_data<< ({{30{1'b0}},dcache_addr[1:0]}<<3));
    
    //===== Sequential Part =====
    always @(posedge clk or posedge reset) begin // PC
        if (reset) begin
            PC          <= `PC_RESET;
            ex_PC       <= `PC_RESET;
            ex_PC_plus4 <= `PC_RESET;
            wb_PC_plus4 <= `PC_RESET;
            icache_addr <= `PC_RESET;
            PC_start    <= 1'b0;
        end
        else if (stall) begin
            PC          <= PC; 
            ex_PC       <= ex_PC;
            ex_PC_plus4 <= ex_PC_plus4;
            wb_PC_plus4 <= wb_PC_plus4;
            icache_addr <= icache_addr;
            PC_start    <= PC_start;
        end
        else if (!PC_start)begin
            PC          <= PC; 
            ex_PC       <= ex_PC;
            ex_PC_plus4 <= ex_PC_plus4;
            wb_PC_plus4 <= wb_PC_plus4;
            icache_addr <= PC_plus4;
            PC_start    <= 1'b1;
        end
        else if (Jump || Branch || ex_Jump || ex_Branch)begin
            PC          <= icache_addr; 
            ex_PC       <= PC;
            ex_PC_plus4 <= PC_plus4;
            wb_PC_plus4 <= ex_PC_plus4;
            icache_addr <= (ex_Jump || (ex_Branch && taken))? ALUout: (wb_Branch || wb_Jump) ? icache_addr+4 : icache_addr;
            PC_start    <= PC_start;
        end
        else begin
            PC          <= icache_addr; 
            ex_PC       <= PC;
            ex_PC_plus4 <= PC_plus4;
            wb_PC_plus4 <= ex_PC_plus4;
            icache_addr <= (ex_Jump || (ex_Branch && taken))? ALUout: icache_addr+4;
            PC_start    <= PC_start;
        end
    end

    always @(posedge clk or posedge reset) begin // Control
        if (reset) begin
            ex_Asel     <= 1'b0;  
            ex_Bsel     <= 1'b0;
            ex_Branch   <= 1'b0;
            ex_MemRead  <= 1'b0;
            ex_MemWrite <= 1'b0;
            ex_MemtoReg <= 1'b0;
            ex_Jump     <= 1'b0;
            ex_regWrite <= 1'b0; 

            wb_MemtoReg <= 1'b0;
            wb_Jump     <= 1'b0;
            wb_Branch   <= 1'b0;
            wb_regWrite <= 1'b0;
        end
        else if (stall) begin
            ex_Asel     <= ex_Asel;  
            ex_Bsel     <= ex_Bsel;
            ex_Branch   <= ex_Branch;
            ex_MemRead  <= ex_MemRead;
            ex_MemWrite <= ex_MemWrite;
            ex_MemtoReg <= ex_MemtoReg;
            ex_Jump     <= ex_Jump; 
            ex_regWrite <= ex_regWrite;

            wb_MemtoReg <= wb_MemtoReg;
            wb_Jump     <= wb_Jump;
            wb_Branch   <= wb_Branch;
            wb_regWrite <= wb_regWrite;
        end
        else if (ex_Jump || ex_Branch || wb_Branch || wb_Jump) begin
            ex_Asel     <= 1'b0;  
            ex_Bsel     <= 1'b0;
            ex_Branch   <= 1'b0;
            ex_MemRead  <= 1'b0;
            ex_MemWrite <= 1'b0;
            ex_MemtoReg <= 1'b0;
            ex_Jump     <= 1'b0; 
            ex_regWrite <= 1'b0; 

            wb_MemtoReg <= ex_MemtoReg;
            wb_Jump     <= ex_Jump;
            wb_Branch   <= ex_Branch;
            wb_regWrite <= ex_regWrite; 
        end
        else begin
            ex_Asel     <= Asel;  
            ex_Bsel     <= Bsel;
            ex_Branch   <= Branch;
            ex_MemRead  <= MemRead;
            ex_MemWrite <= MemWrite;
            ex_MemtoReg <= MemtoReg;
            ex_Jump     <= Jump;
            ex_regWrite <= regWrite; 

            wb_MemtoReg <= ex_MemtoReg;
            wb_Jump     <= ex_Jump;
            wb_Branch   <= ex_Branch;
            wb_regWrite <= ex_regWrite;
        end
    end

    always @(posedge clk or posedge reset) begin // IFID/EX interface
        if (reset) begin
            ex_rs1_data     <= 32'd0; 
            ex_rs2_data     <= 32'd0;
            ex_icache_dout  <= 32'd0;
            ex_rd           <=  5'd0;
            ex_rs1          <=  5'd0;
            ex_rs2          <=  5'd0;

            wb_rd           <=  5'd0;
            wb_funct        <=  3'd0;
        end
        else if (stall) begin
            ex_rs1_data     <= ex_rs1_data; 
            ex_rs2_data     <= ex_rs2_data;
            ex_icache_dout  <= ex_icache_dout;
            ex_rd           <= ex_rd;
            ex_rs1          <= ex_rs1;
            ex_rs2          <= ex_rs2;
            wb_rd           <= wb_rd;
            wb_funct        <= wb_funct;
        end
        else if(ex_Jump || ex_Branch || wb_Branch || wb_Jump)begin
            ex_rs1_data     <= 32'd0; 
            ex_rs2_data     <= 32'd0;
            ex_icache_dout  <= 32'd0;
            ex_rd           <= 5'd0;
            ex_rs1          <= 5'd0;
            ex_rs2          <= 5'd0;
            
            wb_rd           <= ex_rd;
            wb_funct        <= funct;
        end
        else begin
            if (rs1 != 5'd0 && rs1 == wb_rd)
                ex_rs1_data      <= rd_data;
            else ex_rs1_data     <= rs1_data; 
            if (rs2 != 5'd0 && rs2 == wb_rd)
                ex_rs2_data      <= rd_data;
            else ex_rs2_data     <= rs2_data; 
            ex_icache_dout  <= icache_dout;
            ex_rd           <= (icache_dout[6:0] == 7'b0100011) ? 5'd0 : rd;
            ex_rs1          <= rs1;
            ex_rs2          <= rs2;
            wb_rd           <= ex_rd;
            wb_funct        <= funct;
        end
    end

    always @(posedge clk or posedge reset) begin // EX/WB interface
        if (reset) begin
            wb_ALUout   <= 32'd0;
        end
        else if (stall) begin
            wb_ALUout   <= wb_ALUout;
        end
        else begin
            wb_ALUout <= ALUout;
        end
    end

    always @(posedge clk or posedge reset) begin // csr
        if (reset) csr <= 32'dz;
        else if (CSR && !Bsel) csr <= (rs1 == ex_rd) ? ALUout : rs1_data;
        else if (CSR && Bsel) csr <= 32'd0;
        else csr <= csr;
    end
    
    // assertion
    // Upon reset, the program counter should become PC_RESET
    property pc_reset;
        @(posedge clk) 
        reset |=> (PC == `PC_RESET);
    endproperty
    assert property (pc_reset);

    // For store instructions, the write enable mask should have the appropriate number of ones depending on whether the instruction is sb, sh, or sw
    property sb;
        @(posedge clk) 
        (funct == 3'b000 && ex_MemWrite) |-> (dcache_we == (4'b0001 << (dcache_addr[1:0]))); // SB
    endproperty
    assert property (sb);

    property sh;
        @(posedge clk) 
        (funct == 3'b001 && ex_MemWrite) |-> (dcache_we == (4'b0011 << (dcache_addr[1:0]))); // SH
    endproperty
    assert property (sh);

    property sw;
        @(posedge clk) 
        (funct == 3'b010 && ex_MemWrite) |-> (dcache_we == 4'b1111); // SW
    endproperty
    assert property (sw);

    // For lb instructions, the upper 24 bits of data written to the regfile should be all 0s or 1s. For lh instructions, the upper 16 bits of data written to the regfile should be all 0s or 1s
    property lb;
        @(posedge clk) 
        (wb_funct == 3'b000 && wb_MemtoReg) |-> (rd_data[31:8] == {24{1'b1}} || rd_data[31:8] == {24{1'b0}}); // LB
    endproperty
    assert property (lb);

    property lh;
        @(posedge clk) 
        (wb_funct == 3'b001 && wb_MemtoReg) |-> (rd_data[31:16] == {16{1'b1}} || rd_data[31:16] == {16{1'b0}}); // LH
    endproperty
    assert property (lh);
    
endmodule