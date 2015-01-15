-- Simple three-address code/stack language

module CT.Compiler.ThreeAddressCode where

data Register = SP | VR Int deriving (Eq,Show)

data Label = Label String deriving (Eq,Show)

data TacProg = TacProg [TacCommand]

instance Show TacProg where
    show (TacProg cs) = concatMap showCommand cs

data TacCommand = PushReg Register | PushMem Register Register | PopReg Register
                | MoveMem Register Register Register
                | Constant Register Int | ConstLabel Register Label | Labeled Label
                | Unary Register UnaryOp Register | Binary Register Register BinOp Register
                | Move Register Register | BZero Register Label | Jump Label
                | Comment String | PutStr String | PutReg Register
                deriving Show

data UnaryOp = Deref | Neg deriving Show

data BinOp = Plus | Minus | IsEqual | GrtrThan | LessThan deriving Show

showCommand :: TacCommand -> String
showCommand (PushReg reg)           = "\tPushReg " ++ showReg reg ++ "\n"
showCommand (PushMem rBase rBytes)  = "\tPushMem " ++ showReg rBase ++ "[" ++ showReg rBytes ++ "]\n"
showCommand (PopReg reg)            = "\tPopReg " ++ showReg reg ++ "\n"
showCommand (MoveMem rDest rBase rBytes) = "\t" ++ showReg rDest ++ " <== " ++ showReg rBase ++ "[" ++ showReg rBytes ++ "]\n"
showCommand (Constant reg n)        = "\t" ++ showReg reg ++ " := " ++ show n ++ "\n"
showCommand (ConstLabel reg l)      = "\t" ++ showReg reg ++ " := " ++ showLabel l ++ "\n"
showCommand (Labeled l)             = "   " ++ showLabel l ++ ":\n"
showCommand (Unary rD op rS)        = "\t" ++ showReg rD ++ " := " ++ showUOp op ++ showReg rS ++ "\n"
showCommand (Binary rD rA op rB)    = "\t" ++ showReg rD ++ " := " ++ showReg rA ++ " " ++ showBOp op ++ " " ++ showReg rB ++ "\n"
showCommand (Move rD rS)            = "\t" ++ showReg rD ++ " := " ++ showReg rS ++ "\n"
showCommand (BZero reg lab)         = "\tBZero " ++ showReg reg ++ " " ++ showLabel lab ++ "\n"
showCommand (Jump lab)              = "\tJump " ++ showLabel lab ++ "\n"
showCommand (Comment s)             = "\t-- " ++ s ++ "\n"
showCommand (PutStr s)              = "\tPutStr " ++ show s ++ "\n"
showCommand (PutReg r)              = "\tPutReg " ++ showReg r ++ "\n"

showReg :: Register -> String
showReg SP     = "sp"
showReg (VR n) = "r" ++ show n

showLabel :: Label -> String
showLabel (Label n) = n

showUOp :: UnaryOp -> String
showUOp Deref = "*"
showUOp Neg   = "-"

showBOp :: BinOp -> String
showBOp Plus    = "+"
showBOp Minus   = "-"
showBOp IsEqual = "=="
