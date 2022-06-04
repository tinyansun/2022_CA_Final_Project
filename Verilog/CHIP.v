// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    assign rs1 = instruction[19 : 15];
    assign rs2 = instruction[24 : 20];
    assign rd = instruction[11 : 7];
    wire Branch_control;
    wire MemRead_control;
    wire MemWrite_control;
    reg  [1 : 0] MemtoReg_control;
    reg  [1 : 0] ALUOp_control;
    wire ALUSrc_control_1;
    wire ALUSrc_control_2;
    wire jump_select;

    wire [31 : 0] imm_gen_output;

    reg  [3 : 0] ALU_operation;
    wire [31 : 0] ALU_input_1;
    wire [31 : 0] ALU_input_2;
    wire ALU_zero;
    wire [31 : 0] ALU_output;
    
    wire Mem_Read_Write;
    wire [31 : 0] Mem_output;
    assign Mem_Read_Write_control = (MemRead_control) ? 0 : 1;  //memory's implementaion requires only either of MemRead_control or MemWrite_control
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: any combinational/sequential circuit

    Control Control(
        .Op_input(instruction[6 : 0]),
        .Branch_output(Branch_control),
        .MemRead_output(MemRead_control),
        .MemWrite_output(MemWrite_control),
        .MemtoReg_output(MemtoReg_control),
        .ALUOp_output(ALUOp_control),
        .ALUSrc_output_1(ALUSrc_control_1),
        .ALUSrc_output_2(ALUSrc_control_2),
        .RegWrite_output(regWrite),
        .jump_select_output(jump_select)
    );

    // Imm Gen (32 bits in, 32 bits out)
    Sign_Extend Sign_Extend(
        .inst_input (instruction[31 : 0]),
        .imm_output (imm_gen_output)
    );

    // MUX between register and ALU (for rs1 and PC)
    MUX_2_to_1 MUX_reg_to_ALU(
        data1_input(rs1_data),
        data2_input(PC),
        select_input(ALUSrc_control_1),
        data_output(ALU_input_1)                //ALU 1st input
    );

    // MUX between register and ALU (for rs2 and imm_gen output)
    MUX_2_to_1 MUX_reg_to_ALU(
        data1_input(rs2_data),
        data2_input(imm_gen_output),
        select_input(ALUSrc_control_2),
        data_output(ALU_input_2)                //ALU 2nd input
    );

    // ALU Control
    ALU_Control ALU_Control(
        .ALUControl_op_input(ALUOp_control),
        .ALUControl_instruction_input(instruction[31 : 0]),
        .ALUControl_output(ALU_operation)   //ALU_control_op_input
    );

    // ALU
    ALU ALU(
        .ALU_input_1(ALU_input_1),
        .ALU_input_2(ALU_input_2),
        .ALU_control_op_input(ALU_operation),
        .ALU_zero(ALU_zero),
        .ALU_output(ALU_output)
    );

    // memory
    memory memory(
        .clk(clk),
        .rst_n(rst_n),
        .wen(Mem_Read_Write_control),   //0: read; 1: write
        .a(ALU_output),
        .d(rs2_data),
        .q(Mem_output),                 //memory data output
        .offset()
    );

    // MUX between memory and register (for ALU output and read data from memory)
    MUX_3_to_1 MUX_mem_to_reg(
        .data1_input(ALU_output),
        .data2_input(Mem_output),
        .data3_input(),                 //PC+4
        .select_input(MemtoReg_control),
        .data_output(rd_data)           //register write data input
    );

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
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
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2

endmodule

module Control
(
    Op_input,
    Branch_output,
    MemRead_output,
    MemWrite_output,
    MemtoReg_output,
    ALUOp_output,
    ALUSrc_output_1,
    ALUSrc_output_2,
    RegWrite_output,
    jump_select_output
);

input  [6 : 0] Op_input;
output [1 : 0] ALUOp_output;
output         ALUSrc_output_1;
output         ALUSrc_output_2;
output         Branch_output;
output         MemRead_output;
output         MemWrite_output;
output [1 : 0] MemtoReg_output;
output         RegWrite_output;
output         jump_select_output;

reg [1 : 0] ALUOp_reg;
reg [1 : 0] MemtoReg_reg;

assign ALUOp_output = ALUOp_reg;
assign ALUSrc_output_1 = (Op_input == 7'b0010111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // for auipc and jal accessing PC
assign ALUSrc_output_2 = (Op_input == 7'b0000011 || Op_input == 7'b0100011 || Op_input == 7'b0010011 || Op_input == 7'b0010111 || Op_input == 7'b1100111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // 7'b0010111 for auipc accessing imm
assign Branch_output = (Op_input == 7'b1100011)? 1'b1 : 1'b0;                                                                                                                                      // 7'b1100111 for jalr accessing imm
assign MemRead_output = (Op_input == 7'b0000011)? 1'b1 : 1'b0;                                                                                                                                     // 7'b1101111 for jal accessing imm
assign MemWrite_output = (Op_input == 7'b0100011)? 1'b1 : 1'b0;
assign RegWrite_output = (Op_input == 7'b0000011 || Op_input == 7'b0110011 || Op_input == 7'b0010011 || Op_input == 7'b0010111 || Op_input == 7'b1100111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // 7'b0010111 for auipc wb
assign MemtoReg_output = MemtoReg_reg;                                                                                                                                                            // 7'b1100111 for jalr wb
assign jump_select_output = (Op_input == 7'b1100111 || || Op_input == 7'b1101111)? 1'b1 : 1'b0; // for jalr and jal setting PC = rs1 + imm or PC = PC + offset                                    // 7'b1101111 for jal wb

always @(Op_input)
begin
    if (Op_i == 7'b0110011) // R-type inst, MUL, DIV, XOR
	begin
		ALUOp_reg = 2'b10; 
		MemtoReg_reg = 2'b00; // select ALU result to write data
	end
	else if (Op_i == 7'b0010011 || Op_i == 7'b0010111) // I-type inst, auipc, slti, srai
	begin
		ALUOp_reg = 2'b11;
		MemtoReg_reg = 2'b00; // select ALU result to write data
	end
	else if (Op_i == 7'b0000011) // lw inst
	begin
		ALUOp_reg = 2'b00;
		MemtoReg_reg = 2'b01; // select memory result to write data
	end
	else if (Op_i == 7'b0100011) // sw inst
	begin
		ALUOp_reg = 2'b00;
	end
	else if (Op_i == 7'b1100011) // beq inst
	begin
		ALUOp_reg = 2'b01;
	end
    else if (Op_i == 7'b1100111 || Op_i == 7'b1101111) // jalr, jal inst
	begin
        ALUOp_reg = 2'b11;    
        MemtoReg_reg = 2'b10; // select PC+4 result to write data in register
    end
end


endmodule

module Sign_Extend  // Imm Gen : for I-type, load, store, beq, auipc, jalr and jal
(
	inst_input,
	imm_output
);

input  [31 : 0] inst_input;
output [31 : 0] imm_output;

reg [11 : 0] imm_reg;
reg [31 : 0] imm_output_reg;
assign imm_output = imm_output_reg;

always @(inst_input)
begin
	if (inst_input[6 : 0] == 7'b0010011 || inst_input[6 : 0] == 7'b0000011 || inst_input[6 : 0] == 7'b1100111) // I-type, load, jalr
	begin
		imm_reg[11 : 0] = inst_input[31 : 20];
        imm_output_reg = {{20{imm_reg[11]}} , imm_reg[11 : 0]};
	end
	else if (inst_input[6 : 0] == 7'b0100011) // store
	begin
		imm_reg[4 : 0] = inst_input[11 : 7];
		imm_reg[11 : 5] = inst_input[31 : 25];
        imm_output_reg = {{20{imm_reg[11]}} , imm_reg[11 : 0]};
	end
	else if (inst_input[6 : 0] == 7'b1100011) // beq
	begin
		imm_reg[3 : 0] = inst_input[11 : 8];
		imm_reg[9 : 4] = inst_input[30 : 25];
		imm_reg[10] = inst_input[7];
		imm_reg[11] = inst_input[31];
        imm_output_reg = {{20{imm_reg[11]}} , imm_reg[11 : 0]};
	end
    else if (inst_input[6 : 0] == 7'b0010111) // auipc
    begin
        imm_output_reg = {{12{inst_input[31]}} , inst_input[31 : 12]};
    end
    else if (inst_input[6 : 0] == 7'b1101111) // jal
    begin
        imm_reg[9 : 0] = inst_input[30 : 21];
		imm_reg[10] = inst_input[20];
		imm_reg[18 : 11] = inst_input[19 : 12];
		imm_reg[19] = inst_input[31];
        imm_output_reg = {{12{imm_reg[19]}} , imm_reg[19 : 0]};
    end
end

endmodule

module MUX_2_to_1
(
	data1_input,
	data2_input,
	select_input,
	data_output
);

input  [31 : 0] data1_input;
input  [31 : 0] data2_input;
input           select_input;
output [31 : 0] data_output;

assign data_output = (select_input == 1'b0)? data1_input : data2_input;

endmodule

module ALU_Control(
    ALUControl_op_input,
    ALUControl_instruction_input,
    ALUControl_output
);
    
    input  [1:0] ALUControl_op_input;
    input  [3:0] ALUControl_op_func7_func3;
    output [3:0] ALUControl_output;

    reg  [3 : 0] ALUControl_output_reg;
    assign ALUControl_output = ALUControl_output_reg;

    always @(ALUControl_op_input or ALUControl_instruction_input)
    begin
        case(ALUControl_op_input)
            2'b00: ALUControl_output_reg = 4'b0010;//ld,sd add
            2'b01: ALUControl_output_reg = 4'b0110;//bq    subtract
            2'b10: begin
                //Rtype add/sub/AND/OR
                if      ({ALUControl_instruction_input[30],ALUControl_instruction_input[14:12]} == 4'b0000) ALUControl_output_reg = 4'b0010;//add
                else if ({ALUControl_instruction_input[30],ALUControl_instruction_input[14:12]} == 4'b1000) ALUControl_output_reg = 4'b0110;//subtract
                else if ({ALUControl_instruction_input[30],ALUControl_instruction_input[14:12]} == 4'b0111) ALUControl_output_reg = 4'b0000;//AND
                else    ({ALUControl_instruction_input[30],ALUControl_instruction_input[14:12]} == 4'b0110) ALUControl_output_reg = 4'b0001;//OR
            end
            2'b11: //Itype ???
        endcase
    end

endmodule

module ALU(
    ALU_input_1,
    ALU_input_2,
    ALU_control_op_input,
    ALU_zero,
    ALU_output
);
    
    input  [31 : 0] ALU_input_1;
    input  [31 : 0] ALU_input_2;
    input  [3 : 0] ALU_control_op_input;
    output ALU_zero;
    output [31 : 0] ALU_output;

endmodule

module MUX_3_to_1(
    data1_input,
    data2_input,
    data3_input,
    select_input,
    data_output
);

    input  [31 : 0] data1_input;
    input  [31 : 0] data2_input;
    input  [31 : 0] data3_input;
    input  [1 : 0]  select_input;
    output [31 : 0] data_output;

    reg [31 : 0] data_output_reg;
    assign data_output = data_output_reg;

    always @(data1_input, data2_input, data3_input, select_input) begin
        case(select_input)
            2'b00: data_output_reg = data1_input;
            2'b01: data_output_reg = data2_input;
            2'b10: data_output_reg = data3_input;
            2'b11: data_output_reg = 0;
        endcase
    end
endmodule
