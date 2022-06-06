.data
    n: .word 11
.text
.globl __start

FUNCTION:
main:
    addi sp,sp,-8
    sw x1,4(sp)
    sw a0,0(sp)
    slti x6,a0,10
    beq x6,x0,ad 
    slti x6,a0,1
    beq x6,x0,mid
    addi t0,x0,7
    addi sp,sp,8
    jalr x0,0(x1)
 ad:
    add x7,x0,a0
    addi x28,x0, 3
    mul a0,x7,x28 
    addi x28,x0,4
    div a0,a0,x28 
    jal x1,main
    addi x6,t0,0 
    lw a0,0(sp)
    lw x1,4(sp)
    addi sp,sp,8
    slli x6,x6,1 
    addi x28,x0,7
    mul x7,a0,x28 
    addi x28,x0,8
    div x7,x7,x28
    add x6,x6,x7
    addi t0,x0,0
    add t0,t0,x6
    addi t0,t0,-137
    jalr x0,0(x1)
 mid:
    add x7,x0,a0
    addi a0,x7,-1
    jal x1,main
    addi x6,t0,0
    lw a0,0(sp)
    lw x1,4(sp)
    addi sp,sp,8
    slli x6,x6,1
    addi t0,x0,0
    add t0,t0,x6
    jalr x0,0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   a0, 0(t0)
    jal  x1, FUNCTION
    la   a0, n
    sw   t0, 4(a0)
    addi a0,x0,10
    ecall