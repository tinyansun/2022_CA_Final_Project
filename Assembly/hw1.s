.data
    n: .word 11
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    main:
    addi sp,sp,-16
    sw x1,8(sp)
    sw a0,0(sp)
    slti x6,a0,10
    beq x6,x0,ad # n >= 10
    #addi x6,x0, 1  
    slti x6,a0,1
    beq x6,x0,mid
    #bge a0,x6,mid # 1 < n < 10
    addi t0,x0,7
    addi sp,sp,16
    jalr x0,0(x1)
 ad:  # for n >= 10
    add x7,x0,a0
    addi x28,x0, 3
    mul a0,x7,x28 # 3n
    addi x28,x0,4
    div a0,a0,x28 # 3n/4
    jal x1,main
    addi x6,t0,0 #T(3n/4)
    lw a0,0(sp)
    lw x1,8(sp)
    addi sp,sp,16
    slli x6,x6,1 #2T()
    addi x28,x0,7
    mul x7,a0,x28 # 7*n
    addi x28,x0,8
    div x7,x7,x28 # 7n/8 %
    add x6,x6,x7
    addi t0,x0,0
    add t0,t0,x6
    addi t0,t0,-137
    jalr x0,0(x1)
 mid:
    add x7,x0,a0
    addi a0,x7,-1 # n-1
    jal x1,main
    addi x6,t0,0 #T(n-1)
    lw a0,0(sp)
    lw x1,8(sp)
    addi sp,sp,16
    slli x6,x6,1 #2T()
    addi t0,x0,0
    add t0,t0,x6
    jalr x0,0(x1)

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall