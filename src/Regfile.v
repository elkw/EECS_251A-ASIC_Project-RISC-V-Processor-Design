module Regfile(clk, reset, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, reset, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            if (aw == 0) mem_nxt[i] = mem[i];
            else         mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                mem[i] <= 32'h0;
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end

    // assertion
    
    // The x0 register should always be 0
    property x0;
        @(posedge clk) mem[0] == 0;
    endproperty
    assert property (x0);

endmodule