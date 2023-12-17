
module Load_extention(
    input [2:0] func3,
    input [31:0] dcache_dout,
    input [31:0] wb_dcache_addr,
    output reg [31:0] dcache_dout_ld_ext
);

always @* begin
    case(func3)
        3'b000: begin // LB
            if (wb_dcache_addr[1:0] == 2'b00) 
                dcache_dout_ld_ext = { {24{dcache_dout[ 7]}}, dcache_dout[ 7: 0]};
            else if (wb_dcache_addr[1:0] == 2'b01) 
                dcache_dout_ld_ext = { {24{dcache_dout[15]}}, dcache_dout[15: 8]};
            else if (wb_dcache_addr[1:0] == 2'b10) 
                dcache_dout_ld_ext = { {24{dcache_dout[23]}}, dcache_dout[23:16]};
            else 
                dcache_dout_ld_ext = { {24{dcache_dout[31]}}, dcache_dout[31:24]};
        end
        3'b001: begin // LH
            if (wb_dcache_addr[1:0] == 2'b00) 
                dcache_dout_ld_ext = { {16{dcache_dout[15]}}, dcache_dout[15: 0]};
            else 
                dcache_dout_ld_ext = { {16{dcache_dout[31]}}, dcache_dout[31:16]};
        end
        3'b010: // LW
            dcache_dout_ld_ext = dcache_dout;
        3'b100: begin // LBU
            if (wb_dcache_addr[1:0] == 2'b00) 
                dcache_dout_ld_ext = {{24{1'b0}}, dcache_dout[ 7: 0]};
            else if (wb_dcache_addr[1:0] == 2'b01) 
                dcache_dout_ld_ext = {{24{1'b0}}, dcache_dout[15: 8]};
            else if (wb_dcache_addr[1:0] == 2'b10) 
                dcache_dout_ld_ext = {{24{1'b0}}, dcache_dout[23:16]};
            else 
                dcache_dout_ld_ext = {{24{1'b0}}, dcache_dout[31:24]};
        end
        3'b101: begin // LHU
            if (wb_dcache_addr[1:0] == 2'b00) 
                dcache_dout_ld_ext = { {16{1'b0}}, dcache_dout[15: 0]};
            else 
                dcache_dout_ld_ext = { {16{1'b0}}, dcache_dout[31:16]};
        end
        default: dcache_dout_ld_ext = dcache_dout;
    endcase
end

endmodule