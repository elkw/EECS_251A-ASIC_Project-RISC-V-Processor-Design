module Branch_comp(
    input [31:0] A,
    input [31:0] B,
    input [ 2:0] func3,
    output  reg     taken
);

always@(*)begin
    case(func3)
        3'b000:
            begin
                if($signed(A) == $signed(B))
                    taken = 1;
                else
                    taken = 0;
            end
        3'b001:
            begin
                if($signed(A) == $signed(B))
                    taken = 0;
                else
                    taken = 1;
            end
        3'b100:
            begin
                if($signed(A) < $signed(B))
                    taken = 1;
                else
                    taken = 0;
            end
        3'b101:
            begin
                if($signed(A) >= $signed(B))
                    taken = 1;
                else
                    taken = 0;
            end
        3'b110:
            begin
                if(A < B)
                    taken = 1;
                else
                    taken = 0;
            end
        3'b111:
            begin
                if(A >= B)
                    taken = 1;
                else
                    taken = 0;
            end
        default: taken = 0;
    endcase
end
endmodule
