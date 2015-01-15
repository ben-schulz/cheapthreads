{--

 See Note in ETIC/Print.hs

 --}


module ETIC.Template where

import ETIC.Syntax
import Control.Monad.Identity
import Data.List
type M = Identity

genTimer :: M String
genTimer = return $ 
                "IO int TMR0_CTRL_REG at 0x83c00000;\n"++
                "IO int TMR0_LOAD_REG at 0x83c00004;\n"++
                "IO int TMR0_DATA_REG at 0x83c00008;\n"++
                "const int TMR_ENABLE_MASK = 0x4d2;\n"++
                "const int TMR_CLR_MASK = 0x5d2;\n"++
                "\n"++
                "timer_init(int tick_speed_usec)\n" ++
                "{\n"++
                "   TMR0_LOAD_REG <- 50 * tick_speed_usec;\n"++
                "   TMR0_CTRL_REG <- TMR_ENABLE_MASK;\n"++
                "}\n"++
                "\n"++
                "timer_ack()\n"++
                "{\n"++
                "   TMR0_CTRL_REG <- TMR_CLR_MASK;\n"++
                "}\n\n"

-- genLoadImage creates the ETIC to load an image
-- parameters:  String: Name of the Image on Disk,
--              Integer: a unique ID for each image
genLoadImage :: String -> Integer -> M String
genLoadImage img id  = return $ 
                            "image img_" ++ show id ++ " in \"" ++ img ++ "\";\n" ++
                            "const int PID_" ++ show id ++ " = " ++ show id ++ ";\n" ++
                            "queue<int> img_" ++ show id ++ "_maps;\n\n"

                    
-- genInitImage generates init_images(), which initializes the images and adds them to the tlb
-- parameters:  [Integer]: a list of image ID's 
genInitImage :: [Integer] -> M String
genInitImage ids = 
                -- generates the TLB code for each image
                let x = map (\a -> 
                            "   while ((i < img_" ++ show a ++ ".segc))\n" ++
                            "   {\n" ++
                            "       size = img_" ++ show a ++ ".segs[i].size;\n" ++
                            "       j = 0;\n" ++
                            "       while ((size > 0))\n" ++
                            "       {\n" ++
                            "           paddr = ( img_" ++ show a ++ ".segs[i].paddr + ((j * PAGE_SIZE) / 4));\n" ++
                            "           vaddr = ( img_" ++ show a ++ ".segs[i].vaddr + ((j * PAGE_SIZE) / 4));\n" ++
                            "           map(page_id, PID_" ++ show a ++ ", paddr, vaddr, MMAP_DEFAULT_SIZE, MMAP_DEFAULT_ACCESS);\n" ++
                            "           enqueue( img_" ++ show a ++ "_maps, page_id);\n" ++
                            "           page_id = (page_id + 1);\n" ++
                            "           j = (j + 1);\n" ++
                            "           size = (size - PAGE_SIZE);\n" ++
                            "       }\n" ++
                            "       i = (i + 1);\n" ++
                            "   }\n") ids 
                    -- puts each process in the wait queue
                    y = map (\a -> "    enqueue(wq, PID_" ++ show a ++ ");\n") ids
                -- declairs some global variables for TLB stuff, and creates the function to initialize the images
                in  return $ 
                        "const int PAGE_SIZE = 1024;\n" ++
                        "const int MMAP_DEFAULT_SIZE = 0; //4KB \n" ++
                        "const int MMAP_DEFAULT_ACCESS = 3; //RWX \n"++
                        "queue<int> wq; //wait queue\n" ++ 
                        "_etic_init_images()\n" ++
                        "{\n" ++
                        "   int page_id = 0;\n" ++ 
                        "   int i = 0;\n" ++
                        "   int j = 0;\n" ++
                        "   int size = 0;\n" ++
                        "   int paddr;\n" ++
                        "   int vaddr;\n" ++
                        concat x  ++
                        concat y ++
                        "}\n\n"




