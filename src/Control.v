module Control(OpCode, Func, Branch_w, MemRead_w, MemtoReg_w,
            , MemWrite_w, Asel_w, Bsel_w, RegWrite_w, Jump_w, CSR_w);

    input [6:0] OpCode;
    input [2:0] Func;

	output Branch_w;          //beq
	output MemRead_w;         //lw
    output MemtoReg_w;        //lw
    output MemWrite_w;        //sw
    output Asel_w;            //0: rs1, 1:PC
    output Bsel_w;            //0: rs2, 1:immediate
    output RegWrite_w;
    output Jump_w;            //jal, jalr
    output CSR_w;

    reg [8:0] control;
    
    assign {Branch_w, MemRead_w, MemtoReg_w, MemWrite_w, Asel_w, Bsel_w, RegWrite_w, Jump_w, CSR_w} = control;

    always@(*) begin

        case(OpCode)
            7'b0110011 : control <= 9'b000000100; //R-type
            7'b0010011 : control <= 9'b000001100; //I-type
            7'b0100011 : control <= 9'b000101000; //S-type
            7'b1100011 : control <= 9'b100011000; //B-type
            7'b0000011 : control <= 9'b011001100; //Load
            7'b1101111 : control <= 9'b000011110; //jal
            7'b1100111 : control <= 9'b000001110; //jalr
            7'b0010111 : control <= 9'b000011100; //auipc
            7'b0110111 : control <= 9'b000001100; //lui
            7'b1110011 :
                case(Func)
                    3'b001 : control <= 9'b000000001; //CSRW
                    3'b101 : control <= 9'b000001001; //CSRWI
                    default: control <= 9'd0;
                endcase
            default : control <= 9'd0;
    endcase
    end

endmodule