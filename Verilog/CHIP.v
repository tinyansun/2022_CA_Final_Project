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
    // Exception: You may change wire to reg //x`
    reg    [31:0] PC          ;              //
    reg    [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    //-------------------PC part----------------------------------------
	wire [31 : 0] PC_nxt_wire;
	wire[31 : 0] mux_for_jump; // wire between two MUX
	reg [31 : 0] PC_plusfour;
	reg [31 : 0] PC_shift;
	reg [31 : 0] jump_address;
	integer i;
	
	//-------------------PC_end-----------------------------------------
    
    wire Branch_control;
    wire MemRead_control;
    wire MemWrite_control;
	wire  [1 : 0] MemtoReg_control;
    wire  [1 : 0] MemtoReg_control_reg;
    wire  [1 : 0] ALUOp_control;
    wire ALUSrc_control_1;
    wire ALUSrc_control_2;
    wire jump_select;
	
    wire [31 : 0] imm_gen_output;
	
    wire [3 : 0]  ALU_operation;
    wire [31 : 0] ALU_input_1;
    wire [31 : 0] ALU_input_2;
    wire ALU_zero;
    wire [31 : 0] ALU_output;
    wire muldiv_ready;
    
    // wire Mem_Read_Write;
    // wire [31 : 0] Mem_output;
	reg muldiv_valid;
	//--------------------------------assign--------------------------------------------
	
	assign rs1 = mem_rdata_I[19 : 15];
    assign rs2 = mem_rdata_I[24 : 20];
    assign rd = mem_rdata_I[11 : 7];
    // assign Mem_Read_Write_control = (MemRead_control) ? 0 : 1;  //memory's implementaion requires only either of MemRead_control or MemWrite_control
	always@(*)begin
		PC_nxt = PC_nxt_wire;
	end
	//output
	assign mem_wen_D = MemWrite_control;
    assign mem_addr_D = ALU_output; 
    assign mem_wdata_D = rs2_data;

    reg [31 : 0] mem_addr_I_reg;
    assign mem_addr_I = mem_addr_I_reg;

    reg [1 : 0] state;
    reg [1 : 0] state_nxt;
    //---------------------------------wait for mul and div--------------------------------------------
	always @(*)
    begin
        if ((state == 2'd2) & (state_nxt != 2'd2))
        begin
            mem_addr_I_reg = 32'h00010000;
            PC_nxt = PC_nxt - 4;
        end
        else if (state_nxt == 2'd2)
        begin
        end
            PC_nxt = PC_nxt - 4;
        else
        begin
            mem_addr_I_reg = PC;
			PC_nxt = PC_nxt;
        end
    end
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

    Control Control (
        .Op_input(mem_rdata_I[6 : 0]),
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
        .inst_input (mem_rdata_I[31 : 0]),
        .imm_output (imm_gen_output)
    );

    // MUX between register and ALU (for rs1 and PC)
    MUX_2_to_1 MUX_reg_to_ALU(
        .data1_input(rs1_data),
        .data2_input(PC),
        .select_input(ALUSrc_control_1),
        .data_output(ALU_input_1)                //ALU 1st input
    );

    // MUX between register and ALU (for rs2 and imm_gen output)
    MUX_2_to_1 MUX_reg_to_ALU_1(
        .data1_input(rs2_data),
        .data2_input(imm_gen_output),
        .select_input(ALUSrc_control_2),
        .data_output(ALU_input_2)                //ALU 2nd input
    );

    // ALU Control
    ALU_Control ALU_Control(
        .ALUControl_op_input(ALUOp_control),
        .ALUControl_instruction_input(mem_rdata_I[31 : 0]),
        .ALUControl_output(ALU_operation)   //ALU_control_op_input
    );

    // ALU
    ALU ALU(
        .clk(clk),
        .rst_n(rst_n),
        .ALU_input_1(ALU_input_1),
        .ALU_input_2(ALU_input_2),
        .ALU_control_op_input(ALU_operation),
        .muldiv_valid(muldiv_valid),
        .muldiv_ready(muldiv_ready),
        .ALU_zero(ALU_zero),
        .ALU_output(ALU_output)
    );

    // memory
    // memory memory(
    //     .clk(clk),
    //     .rst_n(rst_n),
    //     .wen(Mem_Read_Write_control),   //0: read; 1: write
    //     .a(ALU_output),
    //     .d(rs2_data),
    //     .q(Mem_output),                 //memory data output
    //     .offset()
    // );

    // MUX between memory and register (for ALU output and read data from memory)
    MUX_3_to_1 MUX_mem_to_reg(
        .data1_input(ALU_output),
        .data2_input(mem_rdata_D),
        .data3_input(PC_plusfour),                 //PC+4
        .select_input(MemtoReg_control),
        .data_output(rd_data)           //register write data input
    );
	
	// MUX between PC+4 & PC shift left
    wire branch_select;
    assign branch_select = Branch_control & ALU_zero;
	MUX_2_to_1 MUX_branch(
        .data1_input(PC_plusfour),
        .data2_input(PC_shift),
        .select_input(branch_select),
        .data_output(mux_for_jump)               
    );
	
	// MUX for jump decision
	MUX_2_to_1 MUX_jump(
        .data1_input(mux_for_jump),
        .data2_input(ALU_output),
        .select_input(jump_select),
        .data_output(PC_nxt_wire)               
    );
	
	//----------------------------fsm---------------------------------------------
	reg [5 : 0] counter;
	reg [5 : 0] counter_nxt;
	parameter IDLE = 2'd0;
    parameter SINGLE  = 2'd1;
    parameter MULTIPLE  = 2'd2;
    parameter OUT = 2'd3;
	
	always @(*) begin
		case(state)
			IDLE : begin
				case(ALU_operation)
					1 : begin
						state_nxt = SINGLE;
						muldiv_valid = 0;
					end
					2 : begin
						state_nxt = SINGLE;
						muldiv_valid = 0;
					end
					3 : begin
						state_nxt = SINGLE;
						muldiv_valid = 0;
					end
					4 : begin
						state_nxt = SINGLE;
						muldiv_valid = 0;
					end
					5 : begin
						state_nxt = SINGLE;
						muldiv_valid = 0;
					end
					6 : begin
						state_nxt = MULTIPLE;
						muldiv_valid = 1;
					end
					7 : begin
						state_nxt = MULTIPLE;
						muldiv_valid = 1;
					end
					default : begin
						state_nxt = state;
						muldiv_valid = 0;
					end
				endcase
			end
			SINGLE : begin
				state_nxt = OUT;
				muldiv_valid = 0;
			end
			MULTIPLE : begin
				if(counter == 32)begin
					state_nxt = OUT;
					muldiv_valid = 0;
				end
				else begin
					state_nxt = MULTIPLE;
					muldiv_valid = 0;
				end
			end
			OUT : begin
				state_nxt = IDLE;
				muldiv_valid = 0;
			end
			default : begin
				state_nxt = state;
				muldiv_valid = 0;
			end
		endcase
	end
	
	// counter
	always@(*)begin
		case(state_nxt)
			MULTIPLE : begin
				counter_nxt = counter+1;
			end
			default:begin
				counter_nxt = 0;
			end
		endcase
	end
	
//-----------------------------------PC_comb---------------------------------------

	always@(*)begin
		PC_plusfour = PC + 4;
		PC_shift = PC + imm_gen_output;
	end
	always@(*)begin
		for(i=28; i<=31; i=i+1)begin
			jump_address[i] = PC_plusfour[i];
		end
		for(i=0; i<=25; i=i+1)begin
			jump_address[i+2] = mem_rdata_I[i];
		end
		for(i=0; i<=1; i=i+1)begin
			jump_address[i] = 0;
		end
	end
	
//-----------------------------------sequential part----------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= IDLE;
			counter <= 0;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt;
			counter <= counter_nxt;
        end
    end
	
endmodule
//--------------------------CHIP_module_end---------------------------------------------------------------------------------------

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
output reg [1 : 0] ALUOp_output;
output reg ALUSrc_output_1;
output reg ALUSrc_output_2;
output reg Branch_output;
output reg MemRead_output;
output reg MemWrite_output;
output reg [1 : 0] MemtoReg_output;
output reg RegWrite_output;
output reg jump_select_output;


always @(*)
begin
    ALUSrc_output_1 = (Op_input == 7'b0010111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // for auipc and jal accessing PC
    ALUSrc_output_2 = (Op_input == 7'b0000011 || Op_input == 7'b0100011 || Op_input == 7'b0010011 || Op_input == 7'b0010111 || Op_input == 7'b1100111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // 7'b0010111 for auipc accessing imm
    Branch_output = (Op_input == 7'b1100011)? 1'b1 : 1'b0;                                                                                                                                      // 7'b1100111 for jalr accessing imm
    MemRead_output = (Op_input == 7'b0000011)? 1'b1 : 1'b0;                                                                                                                                     // 7'b1101111 for jal accessing imm
    MemWrite_output = (Op_input == 7'b0100011)? 1'b1 : 1'b0;
    RegWrite_output = (Op_input == 7'b0000011 || Op_input == 7'b0110011 || Op_input == 7'b0010011 || Op_input == 7'b0010111 || Op_input == 7'b1100111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // 7'b0010111 for auipc wb
                                                                                                                                                                                                // 7'b1100111 for jalr wb
    jump_select_output = (Op_input == 7'b1100111 || Op_input == 7'b1101111)? 1'b1 : 1'b0; // for jalr and jal setting PC = rs1 + imm or PC = PC + offset                                    // 7'b1101111 for jal wb
    // ----------------------------------------------------------------------------------------------------
    if (Op_input == 7'b0110011) // R-type inst, MUL, DIV, XOR
    begin
        ALUOp_output = 2'b10; 
        MemtoReg_output = 2'b00; // select ALU result to write data
    end
    else if (Op_input == 7'b0010011 || Op_input == 7'b0010111) // I-type inst, auipc, slti, srai
    begin
        ALUOp_output = 2'b11;
        MemtoReg_output = 2'b00; // select ALU result to write data
    end
    else if (Op_input == 7'b0000011) // lw inst
    begin
        ALUOp_output = 2'b00;
        MemtoReg_output = 2'b01; // select memory result to write data
    end
    else if (Op_input == 7'b0100011) // sw inst
    begin
        ALUOp_output = 2'b00;
    end
    else if (Op_input == 7'b1100011) // beq inst
    begin
        ALUOp_output = 2'b01;
    end
    else if (Op_input == 7'b1100111 || Op_input == 7'b1101111) // jalr, jal inst
    begin
        ALUOp_output = 2'b11;    
        MemtoReg_output = 2'b10; // select PC+4 result to write data in register
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
    reg [19 : 0] imm_21_reg;
	reg [31 : 0] imm_output_reg;
    reg [31 : 0] imm_output_reg_temp;
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
			imm_output_reg_temp = {{20{imm_reg[11]}} , imm_reg[11 : 0]};
            imm_output_reg = imm_output_reg_temp << 1;
		end
		else if (inst_input[6 : 0] == 7'b0010111) // auipc
		begin
			imm_output_reg = {{12{inst_input[31]}} , inst_input[31 : 12]};
		end
		else if (inst_input[6 : 0] == 7'b1101111) // jal
		begin
			// imm_21_reg[10 : 1] = inst_input[30 : 21];
			// imm_21_reg[11] = inst_input[20];
			// imm_21_reg[19 : 12] = inst_input[19 : 12];
			// imm_21_reg[20] = inst_input[31];
			// imm_output_reg = {{11{imm_21_reg[20]}} , imm_21_reg[20 : 0]};
            imm_21_reg[9 : 0] = inst_input[30 : 21];
			imm_21_reg[10] = inst_input[20];
			imm_21_reg[18 : 11] = inst_input[19 : 12];
			imm_21_reg[19] = inst_input[31];
            // imm_21_reg[0] = 0;
			imm_output_reg_temp = {{12{imm_21_reg[19]}} , imm_21_reg[19 : 0] };
            imm_output_reg = imm_output_reg_temp << 1;
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
    input  [1 : 0] ALUControl_op_input;
    input  [31 : 0] ALUControl_instruction_input;
    output [3 : 0] ALUControl_output;

    reg  [3 : 0] ALUControl_output_reg;
    assign ALUControl_output = ALUControl_output_reg;

    always @(ALUControl_op_input or ALUControl_instruction_input)
    begin
        case(ALUControl_op_input)
            2'b00: ALUControl_output_reg = 4'b0001;//lw,sw add
            2'b01: ALUControl_output_reg = 4'b0010;//bq    subtract
            2'b10: begin
                //Rtype add/sub/AND/OR
                if      ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000000000) ALUControl_output_reg = 4'b0001;//add
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0100000000) ALUControl_output_reg = 4'b0010;//subtract
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000000111) ALUControl_output_reg = 4'b0011;//AND
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000000110) ALUControl_output_reg = 4'b0100;//OR
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000000100) ALUControl_output_reg = 4'b0101;//XOR
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000001000) ALUControl_output_reg = 4'b0110;//MUL
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000001100) ALUControl_output_reg = 4'b0111;//DIV
            end
            2'b11: begin
                if      ({ALUControl_instruction_input[14:12],ALUControl_instruction_input[6:0]} == 10'b0100010011)   ALUControl_output_reg = 4'b1000;//SLTI
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0100000101) ALUControl_output_reg = 4'b1001;//SRAI
                else if ({ALUControl_instruction_input[31:25],ALUControl_instruction_input[14:12]} == 10'b0000000001) ALUControl_output_reg = 4'b1010;//SLLI
                else ALUControl_output_reg = 4'b0001;//jal,jalr,addi,auipc
            end
        endcase
    end

endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [3:0]  mode; // mode: 0110: mulu, 0111: divu, //2: and, 3: avg
    output        ready;

    input  [31:0] in_A, in_B;
    output [31:0] out;

    // Definition of states
    parameter IDLE = 2'd0;
    parameter MUL  = 2'd1;
    parameter DIV  = 2'd2;
    parameter OUT  = 2'd3;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo 5: Wire assignments
    assign ready = (state == OUT) ? 1 : 0;
    assign out = (state == OUT) ? shreg[31:0] : 0;

    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid == 0) state_nxt = state;
                else begin
                    case(mode)
                        4'b0110: state_nxt = MUL;
                        4'b0111: state_nxt = DIV;
                        default: state_nxt = IDLE;
                    endcase
                end
            end
            MUL : begin
                if (counter != 31) state_nxt = MUL;
                else               state_nxt = OUT;
            end
            DIV : begin
                if (counter != 31) state_nxt = DIV;
                else               state_nxt = OUT;
            end
            OUT : state_nxt = IDLE;
            default : state_nxt = state;
        endcase
    end

    // Todo 2: Counter
    always @(*) begin
        if (state == MUL || state == DIV) counter_nxt = counter + 1;
        else                              counter_nxt = 0;
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            IDLE: alu_out = 0;
            MUL: begin
                if (shreg[0] == 1) alu_out = {33'b0} + (alu_in + shreg[63:32]);
                else               alu_out = {1'b0,shreg[63:32]};
            end
            DIV: begin
                if (shreg[63:32] >= alu_in) alu_out = {1'b1,shreg[63:32]-alu_in};
                else                        alu_out = {1'b0,shreg[63:32]};
            end
            OUT: alu_out = 0;
            default: alu_out = 0;
        endcase
    end

    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) shreg_nxt = {32'b0,in_A};
                else       shreg_nxt = 0;
            end
            MUL: shreg_nxt = ({32'b0,shreg[31:0]} >> 1) + {alu_out,31'b0};
            DIV: begin
                if (alu_out[32] == 0) shreg_nxt = shreg << 1;
                else                  shreg_nxt = ({alu_out[31:0],shreg[31:0]} << 1) + {64'b1};
                if (counter == 31) begin
                    if (shreg_nxt[63:32] >= alu_in) begin
                        shreg_nxt[63:32] = shreg_nxt[63:32] - alu_in;
                        shreg_nxt[31:0] = (shreg_nxt[31:0] << 1) + {32'b1};
                    end
                    else shreg_nxt[31:0] = (shreg_nxt[31:0] << 1) + {32'b0};
                end
            end
            OUT: shreg_nxt = 0;
            default: shreg_nxt = 0;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 0;
            shreg <= 0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            alu_in <= alu_in_nxt;
            shreg <= shreg_nxt;
        end
    end

endmodule

module ALU(
    clk,
    rst_n,
    ALU_input_1,
    ALU_input_2,
    ALU_control_op_input,
    muldiv_valid,
    muldiv_ready,
    ALU_zero,
    ALU_output
);

    input clk, rst_n;    
    input  [31 : 0] ALU_input_1;
    input  [31 : 0] ALU_input_2;
    input  [3 : 0] ALU_control_op_input;
    input  muldiv_valid;

    output muldiv_ready;
    output ALU_zero;
    output [31 : 0] ALU_output;

    reg ALU_zero_reg;
    reg  [31 : 0] ALU_output_reg;
    wire [31 : 0] ALU_output_wire;
    wire muldiv_ready_wire;
    assign ALU_zero = ALU_zero_reg; //beq (in_1 - in_2 == 0) ? 1 : 0
    // assign ALU_output = ALU_output_reg;
    assign muldiv_ready = muldiv_ready_wire;
    assign ALU_output = (muldiv_ready) ? ALU_output_wire : ALU_output_reg;

    mulDiv mulDiv(
        .clk(clk), 
        .rst_n(rst_n), 
        .valid(muldiv_valid),           //if valid == 0, mulDiv does nothing
        .ready(muldiv_ready_wire), 
        .mode(ALU_control_op_input),  //if (valid == 1) && (op_input == 4'b0110 or 4'b0111), mulDiv works
        .in_A(ALU_input_1), 
        .in_B(ALU_input_2), 
        .out(ALU_output_wire)
    );

    always @(ALU_input_1, ALU_input_2, ALU_control_op_input)
    begin
        case(ALU_control_op_input)
            4'b0001: begin 
                ALU_output_reg = ALU_input_1 + ALU_input_2;
                // muldiv_ready_reg = 1;
            end
            4'b0010: begin
                ALU_output_reg = ALU_input_1 - ALU_input_2;
                if (ALU_output_reg == 32'b0) ALU_zero_reg = 1;
                else                         ALU_zero_reg = 0;
                // muldiv_ready_reg = 1;
            end
            4'b0011: begin
                ALU_output_reg = ALU_input_1 & ALU_input_2;
                // muldiv_ready_reg = 1;
            end
            4'b0100: begin
                ALU_output_reg = ALU_input_1 | ALU_input_2;
                // muldiv_ready_reg = 1;
            end
            4'b0101: begin
                ALU_output_reg = ALU_input_1 ^ ALU_input_2;
                // muldiv_ready_reg = 1;
            end
            4'b1000: begin
                ALU_output_reg = (ALU_input_1 < ALU_input_2) ? 32'd1 : 0;
            end
            4'b1001: begin
                ALU_output_reg = ALU_input_1 >>> ALU_input_2;    
            end
            4'b1010: begin
                ALU_output_reg = ALU_input_1 << ALU_input_2;
            end
            default: begin
                ALU_output_reg = 0;
            end
        endcase
    end

    always @(posedge clk or negedge rst_n)
    begin
        if (!rst_n) begin
            ALU_output_reg <= 0;
            // muldiv_ready_wire <= 0;
        end
        if (clk) begin
            // muldiv_ready_wire <= 0;
        end
    end

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


	
	
