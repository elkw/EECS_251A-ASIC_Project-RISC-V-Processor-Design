module ImmGen(in_imm, out_imm);

    input [31:0] in_imm;

	output reg [31:0] out_imm;

    always @(*)begin
        case(in_imm[6:0])
            //LB, LH, LW, LBU, LHU
            7'b0000011 : out_imm <= {{20{in_imm[31]}},in_imm[31:20]};
            //SB, SH, SW
            7'b0100011 : out_imm <= {{20{in_imm[31]}},in_imm[31:25],in_imm[11:7]};
            //BEQ, BNE, BLT, BGE, BLTU, BGEU
            7'b1100011 : out_imm <= {{19{in_imm[31]}},in_imm[31],in_imm[7],in_imm[30:25],in_imm[11:8], {1{1'b0}}};
            //ADDI, SLTI, SLTIU, XORI, ORI, ANDI
            7'b0010011 : 
                case(in_imm[14:12])
                    3'b101 : out_imm <= {{27{in_imm[31]}},in_imm[24:20]};
                    default: out_imm <= {{20{in_imm[31]}},in_imm[31:20]};
                endcase
            //JALR
            7'b1100111 : out_imm <= {{20{in_imm[31]}},in_imm[31:20]};
            //JAL
            7'b1101111 : out_imm <= {{11{in_imm[31]}},in_imm[31],in_imm[19:12],in_imm[20],in_imm[30:21], {1{1'b0}}};
            //AUIPC
            7'b0010111 : out_imm <= {in_imm[31:12],{12{1'd0}}};
            //LUI
            7'b0110111 : out_imm <= {in_imm[31:12],{12{1'd0}}};
            //CSRWI
            7'b0110111 : out_imm <= {{27{1'd0}}, in_imm[19:15]};

            default : out_imm <= {32{1'd0}};
        endcase
    end 
endmodule