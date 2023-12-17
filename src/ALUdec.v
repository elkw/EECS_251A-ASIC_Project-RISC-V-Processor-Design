// Module: ALUdecoder
// Desc:   Sets the ALU operation
// Inputs: opcode: the top 6 bits of the instruction
//         funct: the funct, in the case of r-type instructions
//         add_rshift_type: selects whether an ADD vs SUB, or an SRA vs SRL
// Outputs: ALUop: Selects the ALU's operation
//

`include "Opcode.vh"
`include "ALUop.vh"

module ALUdec(
    input [6:0]       opcode,
    input [2:0]       funct,
    input             add_rshift_type,
    output reg [3:0]  ALUop
);

    // Implement your ALU decoder here, then delete this comment
    always@(*)begin
        case(opcode)
            `OPC_LUI: ALUop = `ALU_COPY_B;
            `OPC_ARI_RTYPE:  begin
                case(funct)
                    `FNC_ADD_SUB: ALUop = (add_rshift_type) ? `ALU_SUB : `ALU_ADD;
                    `FNC_SLL    : ALUop = `ALU_SLL;
                    `FNC_SLT    : ALUop = `ALU_SLT;
                    `FNC_SLTU   : ALUop = `ALU_SLTU;
                    `FNC_XOR    : ALUop = `ALU_XOR;
                    `FNC_OR     : ALUop = `ALU_OR;
                    `FNC_AND    : ALUop = `ALU_AND;
                    `FNC_SRL_SRA: ALUop = (add_rshift_type) ? `ALU_SRA : `ALU_SRL;
                endcase
            end
            `OPC_ARI_ITYPE:  begin
                case(funct)
                    `FNC_ADD_SUB: ALUop = `ALU_ADD;
                    `FNC_SLL    : ALUop = `ALU_SLL;
                    `FNC_SLT    : ALUop = `ALU_SLT;
                    `FNC_SLTU   : ALUop = `ALU_SLTU;
                    `FNC_XOR    : ALUop = `ALU_XOR;
                    `FNC_OR     : ALUop = `ALU_OR;
                    `FNC_AND    : ALUop = `ALU_AND;
                    `FNC_SRL_SRA: ALUop = (add_rshift_type) ? `ALU_SRA : `ALU_SRL;
                endcase
            end
            default   : ALUop = `ALU_ADD;
        endcase
    end

endmodule
