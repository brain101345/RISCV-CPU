//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//M_stall
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata                                                        //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
    parameter S_IDLE = 4'd0;
    parameter S_AUPIC = 4'd1;
    parameter S_JAL = 4'd2;
    parameter S_JALR = 4'd3;
    parameter S_ADD = 4'd4;
    parameter S_ADDI = 4'd5;
    parameter S_LW  = 4'd6;
    parameter S_SW  = 4'd7;
    parameter S_MUL = 4'd8;
    parameter S_BEQ = 4'd9;
    parameter S_WAIT_MUL = 4'd10;
    parameter S_WAIT_MEM = 4'd11;
    parameter S_NOP = 4'd12;
    
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC, PC_imm;
        reg [3:0] state, next_state;        
        reg [BIT_W-1:0] ALU_out;
        reg Zero, Branch, Regwrite;
     
        wire o_done, i_valid;
        wire [64-1:0] o_data;
        wire [BIT_W-1:0] rdata1, rdata2;
        wire wen;
        wire [BIT_W-1:0] wdata;
        wire [4:0] rs1, rs2, rd;
        

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
        assign o_IMEM_addr = PC;
        assign o_IMEM_cen = (state == S_IDLE) ? 1'b1 : 1'b0;
        assign i_valid = (state == S_MUL) ? 1'b1 : 1'b0;
        assign o_DMEM_cen = ((state == S_SW)||(state == S_LW)) ? 1'b1 : 1'b0;
        assign o_DMEM_wen = (state == S_SW) ? 1'b1 : 1'b0;
        assign o_DMEM_wdata = rdata2;
        assign o_DMEM_addr = ALU_out;
        assign wen = Regwrite;
        assign wdata = (state == S_WAIT_MEM) ? i_DMEM_rdata : (state == S_WAIT_MUL) ? o_data[31:0] : ALU_out;
        assign rs1 = i_IMEM_data[19:15];
        assign rs2 = i_IMEM_data[24:20];
        assign rd = i_IMEM_data[11:7];
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (wen),          
        .rs1    (rs1),                
        .rs2    (rs2),                
        .rd     (rd),                 
        .wdata  (wdata),             
        .rdata1 (rdata1),           
        .rdata2 (rdata2)
    );
    MULDIV_unit mul0(
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n), 
        .i_valid(i_valid),
        .i_A(rdata1),
        .i_B(rdata2),
        .o_data(o_data),
        .o_done(o_done)

    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    //Branch
    always @(*) begin
        case (i_IMEM_data[6:0])
            7'b1101111, 7'b1100111, 7'b1100011: Branch = 1'b1;
            default: Branch = 1'b0;
        endcase
    end
    //Zero
    always @(*) begin
        if (state == S_BEQ) begin
            case (i_IMEM_data[14:12])
                3'b000: Zero = (rdata1 == rdata2) ? 1'b1 : 1'b0;//BEQ
                3'b101: Zero = ($signed(rdata1) >= $signed(rdata2)) ? 1'b1 : 1'b0;//BGE
                3'b100: Zero = ($signed(rdata1) < $signed(rdata2)) ? 1'b1 : 1'b0;//BLT
                default: Zero = ($signed(rdata1) != $signed(rdata2)) ? 1'b1 : 1'b0;//BNE
            endcase
        end
        else
            Zero = 1'b1; 
    end

    //PC_imm
    always @(*) begin
        if(i_IMEM_data[6:0] ==  7'b1101111) //JAL
            PC_imm = PC + {{11{i_IMEM_data[31]}},{i_IMEM_data[31],i_IMEM_data[19:12],i_IMEM_data[20],i_IMEM_data[30:21],1'b0}};
        else if(i_IMEM_data[6:0] ==  7'b1100011) //BEQ那行
            PC_imm = PC + {{19{i_IMEM_data[31]}},{i_IMEM_data[31],i_IMEM_data[7],i_IMEM_data[30:25],i_IMEM_data[11:8],1'b0}};       
        else //JALR
            PC_imm = rdata1 + {{20{i_IMEM_data[31]}},{i_IMEM_data[31:20]}};

    end

    //next_PC
    always @(*) begin
        case (state)
            S_WAIT_MUL: begin
                if(o_done)
                    next_PC = (Branch & Zero) ? PC_imm : (PC + 32'd4);
                else
                    next_PC = PC;
            end
            S_WAIT_MEM: begin
                if(i_DMEM_stall)
                    next_PC = PC;
                else
                    next_PC = (Branch & Zero) ? PC_imm : (PC + 32'd4);
            end
            S_IDLE, S_MUL, S_LW, S_SW: next_PC = PC;
            default: next_PC = (Branch & Zero) ? PC_imm : (PC + 32'd4);
        endcase     
    end

    //ALU_out
    always @(*) begin
        case (state)
            S_ADD: begin
                if(i_IMEM_data[31:25] == 7'b0100000)//SUB
                    ALU_out = rdata1 - rdata2;
                else begin
                    if(i_IMEM_data[14:12] == 3'b000)//ADD
                        ALU_out = rdata1 + rdata2;
                    else if(i_IMEM_data[14:12] == 3'b111)//AND
                        ALU_out = rdata1 & rdata2;
                    else//XOR
                        ALU_out = rdata1 ^ rdata2;
                end
            end
            S_ADDI: begin
                case (i_IMEM_data[14:12])
                    3'b000:  ALU_out = rdata1 + {{20{i_IMEM_data[31]}},i_IMEM_data[31:20]};//ADDI
                    3'b010:  ALU_out = ($signed(rdata1) < $signed({{20{i_IMEM_data[31]}},i_IMEM_data[31:20]})) ? 1 : 0 ;//SLTI
                    3'b001:  ALU_out = rdata1 << i_IMEM_data[24:20];//SLLI
                    default: ALU_out = $signed(rdata1) >>> i_IMEM_data[24:20];//SRAI
                endcase
            end
            S_AUPIC: ALU_out = PC + {i_IMEM_data[31:12],12'b0};
            S_JAL, S_JALR: ALU_out = PC + 32'd4;
            S_SW: ALU_out = rdata1 +  {{20{i_IMEM_data[31]}},{i_IMEM_data[31:25],i_IMEM_data[11:7]}};
            S_LW: ALU_out = rdata1 +  {{20{i_IMEM_data[31]}},i_IMEM_data[31:20]};
            default: ALU_out = rdata1;
        endcase
    end

    //Regwrite
    always @(*) begin
        case (state)
            S_IDLE,S_LW, S_SW, S_NOP, S_BEQ, S_MUL: Regwrite = 1'b0;
            S_WAIT_MUL: Regwrite = o_done ? 1'b1 : 1'b0;
            S_WAIT_MEM: Regwrite = (i_IMEM_data[6:0] == 7'b0100011) ? 1'b0 : i_DMEM_stall ? 1'b0 : 1'b1;
            default: Regwrite = 1'b1;
        endcase
    end

    //FSM
    always @(*) begin
        case (state)
            S_IDLE: begin
                case (i_IMEM_data[6:0])
                    7'b0010111: next_state = S_AUPIC;
                    7'b1101111: next_state = S_JAL;
                    7'b1100111: next_state = S_JALR;                    
                    7'b0110011: next_state = (i_IMEM_data[31:25] == 7'b0000001)? S_MUL : S_ADD;
                    7'b0010011: next_state = S_ADDI;
                    7'b0000011: next_state = S_LW;
                    7'b0100011: next_state = S_SW;
                    7'b1100011: next_state = S_BEQ;
                    default: next_state = S_NOP;
                endcase
            end
            S_MUL: next_state = S_WAIT_MUL;
            S_SW, S_LW: next_state = S_WAIT_MEM;
            S_WAIT_MUL: next_state = o_done ? S_IDLE : state;
            S_WAIT_MEM: next_state = i_DMEM_stall ? state : S_IDLE;
            S_NOP: next_state = S_NOP;
            default: next_state = S_IDLE;
        endcase
        
    end
    //CS
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= S_IDLE;
        end
        else begin
            PC <= next_PC;
            state <= next_state;            
        end
    end
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit #(
    parameter DATA_W = 32
)
(
    input                       i_clk,
    input                       i_rst_n,

    input                       i_valid,
    input [DATA_W - 1 : 0]      i_A,
    input [DATA_W - 1 : 0]      i_B,

    output [2*DATA_W - 1 : 0]   o_data,
    output                      o_done
);
// Do not Modify the above part !!!

// Parameters
    // Definition of states
    parameter S_IDLE = 4'd0;
    parameter S_MUL = 4'd7;
    parameter S_OUT = 4'd9;

// Wires & Regs
    // Todo
    reg  [3:0] state, next_state;
    reg  [5:0] counter, counter_next;
    reg  [63:0] shift_reg, shift_reg_next;
    reg  [31:0] operand_reg, operand_reg_next;
    reg  [32:0] alu_out;
    reg  done;
// Wire Assignments
    // Todo
    assign o_data = shift_reg;
    assign o_done = done;
// Always Combination
    // Todo: FSM
        always @(*) begin
            case(state)
                S_IDLE  :
                    if(!i_valid)
                        next_state = state;
                    else 
                        next_state = S_MUL;
                S_MUL   : begin
                    if(counter == 31)
                        next_state = S_OUT;
                    else
                        next_state = state;
                end
                S_OUT   : next_state = S_IDLE;
                default : next_state = state;
            endcase
        end
    // Todo: Counter
        always @(*) begin
            if(state == S_MUL)
                counter_next <= counter + 5'd1;
            else
                counter_next <= 5'd0;
        end
    // alu_in
        always @(*) begin
            case(state)
                S_IDLE: begin
                    if(i_valid) operand_reg_next = i_B;
                    else operand_reg_next = operand_reg;
                end
                default: operand_reg_next = operand_reg;
            endcase            
        end
    // Todo: ALU output
        always @(*) begin
            case(state)
                S_MUL: begin
                    if(shift_reg[0] == 1'b1)
                        alu_out = operand_reg[31:0] + shift_reg[63:32];
                    else 
                        alu_out = shift_reg[63:32];
                end
                default: alu_out = 32'd0;
            endcase
        end
    // Todo: Shift register
        always @(*) begin
            case (state)
                S_IDLE: begin
                    if(i_valid) shift_reg_next = {32'd0,i_A[31:0]};
                    else shift_reg_next = shift_reg;
                end 
                S_MUL: begin
                    shift_reg_next = ({alu_out[32:0],shift_reg[31:0]}>>1);
                end
                S_OUT: shift_reg_next = shift_reg;
                default: shift_reg_next = {32'd0,alu_out[31:0]};
            endcase
        end
    // done
        always @(*) begin
            if(state == S_OUT) done = 1'b1;
            else done = 1'b0;
        end
    // Todo: Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state <= S_IDLE;
            shift_reg <= 64'd0;
            
        end
        else begin
            state <= next_state;
            operand_reg <= operand_reg_next;
            shift_reg <= shift_reg_next;
            counter <= counter_next;
        end
    end

endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W-1:0]  o_mem_wdata,
            input [BIT_W-1:0] i_mem_rdata,
            input i_mem_stall
    );

    //---------------------------------------//
    //          default connection           //
        reg [1:0] state, nxt_state;
        reg [55:0] sram [0:127];     // 1 bit valid, 23 bits Tag, 32 bits data
        reg [55:0] sram_tem;
        reg [31:0] read_hit_data;
        reg [22:0] tag_prev;
        reg [6:0] index_prev;
        reg read_hit;

        wire [31:0] read_hit_data_nxt;
        wire [22:0] tag;
        wire [6:0] index;
        wire hit, write_bit, read_bit;
        wire read_hit_nxt;

        integer i;

        assign tag = (state == 1'd0) ? i_proc_addr[31:9] : tag_prev;
        assign index = (state == 1'd0) ? i_proc_addr[8:2] : index_prev;
        assign hit = sram[index][55] & (sram[index][54:32] == tag);
        assign o_mem_addr = i_proc_addr;
        assign o_mem_wdata = i_proc_wdata;
        assign o_proc_rdata = read_hit ? read_hit_data : i_mem_rdata;
        // assign o_proc_rdata = i_mem_rdata;
        assign o_proc_stall = i_mem_stall;
        assign write_bit = i_proc_wen & i_proc_cen;
        assign read_bit = i_proc_cen & !i_proc_wen;
        assign o_mem_wen = write_bit;
        assign o_mem_cen = (read_bit & !hit) | write_bit;
        assign read_hit_nxt = (hit & read_bit);
        assign read_hit_data_nxt = sram[index][31:0];


    //---------------------------------------//
    //             states                    //

    // 2'd0 = IDLE, 2'd1 = READ, 2'd2 = WRITE

    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n)
            state <= 2'b0;
        else
            state <= nxt_state;
    end

    always @(*) begin
        case(state)
            2'd0 : begin
                if(i_proc_cen & !i_proc_wen & !hit)
                    nxt_state = 2'd1;
                else if(i_proc_cen & i_proc_wen )
                    nxt_state = 2'd2;
                else
                    nxt_state = 2'd0;
            end
            2'd1 : nxt_state = i_mem_stall ? 2'd1 : 2'd0;
            2'd2 : nxt_state = i_mem_stall ? 2'd2 : 2'd0;
            default : nxt_state = 2'd0;
        endcase
    end

    always @(*) begin
        sram_tem = 56'b0;
        if(state == 2'd1 & !i_mem_stall) begin
            sram_tem = {1'b1, tag, i_mem_rdata};
        end
        else if(state == 2'd0 & write_bit) begin
            sram_tem = {1'b1, tag, i_proc_wdata};
        end
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n)
            read_hit <= 1'b0;
        else
            read_hit <= read_hit_nxt;
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n)
            read_hit_data <= 32'b0;
        else
            read_hit_data <= read_hit_data_nxt;
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n) begin
            tag_prev <= 23'b0;
            index_prev <= 7'b0;
        end
        else begin
            tag_prev <= tag;
            index_prev <= index;
        end
    end

    //---------------------------------------//

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (i = 0; i < 128; i = i + 1) begin
                sram[i] <= 56'b0;
            end
        end
        else if(state == 2'd1 & !i_mem_stall) begin
            sram[index] <= sram_tem;
        end
        else if(state == 2'd0 & write_bit) begin
            sram[index] <= sram_tem;
        end
    end
    // Todo: BONUS
endmodule