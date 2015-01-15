module Qmonad where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

{-
-- FSM SIGNAL DEFINITIONS - name, type
SIGS:
local_data, std_logic_vector(0 to DATA_WIDTH-1);
empty, std_logic;
full, std_logic;
busy, std_logic;
output, std_logic_vector(0 to DATA_WIDTH-1);
head_ptr, std_logic_vector(0 to ADDR_WIDTH-1);
tail_ptr, std_logic_vector(0 to ADDR_WIDTH-1);
-}
-- Using Int to model bitstrings is admittedly only approximate.
type Addr   = Int
type Data   = Int
type Memory = Addr -> Data
data Bit        = Zero | One deriving Eq
data BitString  = BS [Bit]
showBit Zero = '0'
showBit One  = '1'
instance Show Bit where
    show Zero = "0"
    show One  = "1"
addr_width, data_width :: Int
addr_width = 2 ^ 9
data_width = 2 ^ 8
all_zeros, all_ones :: Addr
all_zeros  = 0
all_ones   = addr_width - 1
{-
GENERICS:
ADDR_WIDTH, integer, 9;
DATA_WIDTH, integer, 8;
MEMS:
mem, DATA_WIDTH, ADDR_WIDTH;
-}


--
-- Monad declarations
--

newtype K a = K {deK :: (Bit ->
                         Bit ->
                         Bit ->
                         Bit ->
                         Bit ->
                         Addr ->
                         Addr ->
                         Data ->
                         Data ->
                         Memory ->
                         ((((((((((a, Bit), Bit), Bit), Bit), Bit), Addr), Addr), Data),
                           Data),
                          Memory))}
instance Prelude.Monad K
    where return = \x_0 -> K (\s_1 -> \s_2 -> \s_3 -> \s_4 -> \s_5 -> \s_6 -> \s_7 -> \s_8 -> \s_9 -> \s_10 -> ((((((((((x_0,
                                                                                                                         s_1),
                                                                                                                        s_2),
                                                                                                                       s_3),
                                                                                                                      s_4),
                                                                                                                     s_5),
                                                                                                                    s_6),
                                                                                                                   s_7),
                                                                                                                  s_8),
                                                                                                                 s_9),
                                                                                                                s_10))
          (>>=) = \x_11 -> \f_12 -> K $ (\s0_13 -> \s0_14 -> \s0_15 -> \s0_16 -> \s0_17 -> \s0_18 -> \s0_19 -> \s0_20 -> \s0_21 -> \s0_22 -> (\(v_23,
                                                                                                                                                         s1_24) -> (\(v_25,
                                                                                                                                                                      s1_26) -> (\(v_27,
                                                                                                                                                                                   s1_28) -> (\(v_29,
                                                                                                                                                                                                s1_30) -> (\(v_31,
                                                                                                                                                                                                             s1_32) -> (\(v_33,
                                                                                                                                                                                                                          s1_34) -> (\(v_35,
                                                                                                                                                                                                                                       s1_36) -> (\(v_37,
                                                                                                                                                                                                                                                    s1_38) -> (\(v_39,
                                                                                                                                                                                                                                                                 s1_40) -> (\(v_41,
                                                                                                                                                                                                                                                                              s1_42) -> deK (f_12 v_41) s1_42) v_39 s1_40) v_37 s1_38) v_35 s1_36) v_33 s1_34) v_31 s1_32) v_29 s1_30) v_27 s1_28) v_25 s1_26) v_23 s1_24) (deK x_11 s0_13 s0_14 s0_15 s0_16 s0_17 s0_18 s0_19 s0_20 s0_21 s0_22))
getDeqK = K (\s_43 -> \s_44 -> \s_45 -> \s_46 -> \s_47 -> \s_48 -> \s_49 -> \s_50 -> \s_51 -> \s_52 -> ((((((((((s_43,
                                                                                                                 s_43),
                                                                                                                s_44),
                                                                                                               s_45),
                                                                                                              s_46),
                                                                                                             s_47),
                                                                                                            s_48),
                                                                                                           s_49),
                                                                                                          s_50),
                                                                                                         s_51),
                                                                                                        s_52))
putDeqK = \x_53 -> K (\_ -> \s_54 -> \s_55 -> \s_56 -> \s_57 -> \s_58 -> \s_59 -> \s_60 -> \s_61 -> \s_62 -> (((((((((((),
                                                                                                                       x_53),
                                                                                                                      s_54),
                                                                                                                     s_55),
                                                                                                                    s_56),
                                                                                                                   s_57),
                                                                                                                  s_58),
                                                                                                                 s_59),
                                                                                                                s_60),
                                                                                                               s_61),
                                                                                                              s_62))
updateDeqK = \f_63 -> getDeqK >>= (\s_64 -> putDeqK (f_63 s_64) >> getDeqK)
getEnqK = K (\s_65 -> \s0_66 -> \s0_67 -> \s0_68 -> \s0_69 -> \s0_70 -> \s0_71 -> \s0_72 -> \s0_73 -> \s0_74 -> ((((((((((s0_66,
                                                                                                                          s_65),
                                                                                                                         s0_66),
                                                                                                                        s0_67),
                                                                                                                       s0_68),
                                                                                                                      s0_69),
                                                                                                                     s0_70),
                                                                                                                    s0_71),
                                                                                                                   s0_72),
                                                                                                                  s0_73),
                                                                                                                 s0_74))
putEnqK = \x_75 -> K (\s_76 -> \s0_77 -> \s0_78 -> \s0_79 -> \s0_80 -> \s0_81 -> \s0_82 -> \s0_83 -> \s0_84 -> \s0_85 -> (((((((((((),
                                                                                                                                   s_76),
                                                                                                                                  x_75),
                                                                                                                                 s0_78),
                                                                                                                                s0_79),
                                                                                                                               s0_80),
                                                                                                                              s0_81),
                                                                                                                             s0_82),
                                                                                                                            s0_83),
                                                                                                                           s0_84),
                                                                                                                          s0_85))
updateEnqK = \f_86 -> getEnqK >>= (\s_87 -> putEnqK (f_86 s_87) >> getEnqK)
getBusyK = K (\s_88 -> \s0_89 -> \s0_90 -> \s0_91 -> \s0_92 -> \s0_93 -> \s0_94 -> \s0_95 -> \s0_96 -> \s0_97 -> ((((((((((s0_90,
                                                                                                                           s_88),
                                                                                                                          s0_89),
                                                                                                                         s0_90),
                                                                                                                        s0_91),
                                                                                                                       s0_92),
                                                                                                                      s0_93),
                                                                                                                     s0_94),
                                                                                                                    s0_95),
                                                                                                                   s0_96),
                                                                                                                  s0_97))
putBusyK = \x_98 -> K (\s_99 -> \s0_100 -> \s0_101 -> \s0_102 -> \s0_103 -> \s0_104 -> \s0_105 -> \s0_106 -> \s0_107 -> \s0_108 -> (((((((((((),
                                                                                                                                             s_99),
                                                                                                                                            s0_100),
                                                                                                                                           x_98),
                                                                                                                                          s0_102),
                                                                                                                                         s0_103),
                                                                                                                                        s0_104),
                                                                                                                                       s0_105),
                                                                                                                                      s0_106),
                                                                                                                                     s0_107),
                                                                                                                                    s0_108))
updateBusyK = \f_109 -> getBusyK >>= (\s_110 -> putBusyK (f_109 s_110) >> getBusyK)
getEmptyK = K (\s_111 -> \s0_112 -> \s0_113 -> \s0_114 -> \s0_115 -> \s0_116 -> \s0_117 -> \s0_118 -> \s0_119 -> \s0_120 -> ((((((((((s0_114,
                                                                                                                                      s_111),
                                                                                                                                     s0_112),
                                                                                                                                    s0_113),
                                                                                                                                   s0_114),
                                                                                                                                  s0_115),
                                                                                                                                 s0_116),
                                                                                                                                s0_117),
                                                                                                                               s0_118),
                                                                                                                              s0_119),
                                                                                                                             s0_120))
putEmptyK = \x_121 -> K (\s_122 -> \s0_123 -> \s0_124 -> \s0_125 -> \s0_126 -> \s0_127 -> \s0_128 -> \s0_129 -> \s0_130 -> \s0_131 -> (((((((((((),
                                                                                                                                                s_122),
                                                                                                                                               s0_123),
                                                                                                                                              s0_124),
                                                                                                                                             x_121),
                                                                                                                                            s0_126),
                                                                                                                                           s0_127),
                                                                                                                                          s0_128),
                                                                                                                                         s0_129),
                                                                                                                                        s0_130),
                                                                                                                                       s0_131))
updateEmptyK = \f_132 -> getEmptyK >>= (\s_133 -> putEmptyK (f_132 s_133) >> getEmptyK)
getFullK = K (\s_134 -> \s0_135 -> \s0_136 -> \s0_137 -> \s0_138 -> \s0_139 -> \s0_140 -> \s0_141 -> \s0_142 -> \s0_143 -> ((((((((((s0_138,
                                                                                                                                     s_134),
                                                                                                                                    s0_135),
                                                                                                                                   s0_136),
                                                                                                                                  s0_137),
                                                                                                                                 s0_138),
                                                                                                                                s0_139),
                                                                                                                               s0_140),
                                                                                                                              s0_141),
                                                                                                                             s0_142),
                                                                                                                            s0_143))
putFullK = \x_144 -> K (\s_145 -> \s0_146 -> \s0_147 -> \s0_148 -> \s0_149 -> \s0_150 -> \s0_151 -> \s0_152 -> \s0_153 -> \s0_154 -> (((((((((((),
                                                                                                                                               s_145),
                                                                                                                                              s0_146),
                                                                                                                                             s0_147),
                                                                                                                                            s0_148),
                                                                                                                                           x_144),
                                                                                                                                          s0_150),
                                                                                                                                         s0_151),
                                                                                                                                        s0_152),
                                                                                                                                       s0_153),
                                                                                                                                      s0_154))
updateFullK = \f_155 -> getFullK >>= (\s_156 -> putFullK (f_155 s_156) >> getFullK)
getHeadPtrK = K (\s_157 -> \s0_158 -> \s0_159 -> \s0_160 -> \s0_161 -> \s0_162 -> \s0_163 -> \s0_164 -> \s0_165 -> \s0_166 -> ((((((((((s0_162,
                                                                                                                                        s_157),
                                                                                                                                       s0_158),
                                                                                                                                      s0_159),
                                                                                                                                     s0_160),
                                                                                                                                    s0_161),
                                                                                                                                   s0_162),
                                                                                                                                  s0_163),
                                                                                                                                 s0_164),
                                                                                                                                s0_165),
                                                                                                                               s0_166))
putHeadPtrK = \x_167 -> K (\s_168 -> \s0_169 -> \s0_170 -> \s0_171 -> \s0_172 -> \s0_173 -> \s0_174 -> \s0_175 -> \s0_176 -> \s0_177 -> (((((((((((),
                                                                                                                                                  s_168),
                                                                                                                                                 s0_169),
                                                                                                                                                s0_170),
                                                                                                                                               s0_171),
                                                                                                                                              s0_172),
                                                                                                                                             x_167),
                                                                                                                                            s0_174),
                                                                                                                                           s0_175),
                                                                                                                                          s0_176),
                                                                                                                                         s0_177))
updateHeadPtrK = \f_178 -> getHeadPtrK >>= (\s_179 -> putHeadPtrK (f_178 s_179) >> getHeadPtrK)
getTailPtrK = K (\s_180 -> \s0_181 -> \s0_182 -> \s0_183 -> \s0_184 -> \s0_185 -> \s0_186 -> \s0_187 -> \s0_188 -> \s0_189 -> ((((((((((s0_186,
                                                                                                                                        s_180),
                                                                                                                                       s0_181),
                                                                                                                                      s0_182),
                                                                                                                                     s0_183),
                                                                                                                                    s0_184),
                                                                                                                                   s0_185),
                                                                                                                                  s0_186),
                                                                                                                                 s0_187),
                                                                                                                                s0_188),
                                                                                                                               s0_189))
putTailPtrK = \x_190 -> K (\s_191 -> \s0_192 -> \s0_193 -> \s0_194 -> \s0_195 -> \s0_196 -> \s0_197 -> \s0_198 -> \s0_199 -> \s0_200 -> (((((((((((),
                                                                                                                                                  s_191),
                                                                                                                                                 s0_192),
                                                                                                                                                s0_193),
                                                                                                                                               s0_194),
                                                                                                                                              s0_195),
                                                                                                                                             s0_196),
                                                                                                                                            x_190),
                                                                                                                                           s0_198),
                                                                                                                                          s0_199),
                                                                                                                                         s0_200))
updateTailPtrK = \f_201 -> getTailPtrK >>= (\s_202 -> putTailPtrK (f_201 s_202) >> getTailPtrK)
getOutputK = K (\s_203 -> \s0_204 -> \s0_205 -> \s0_206 -> \s0_207 -> \s0_208 -> \s0_209 -> \s0_210 -> \s0_211 -> \s0_212 -> ((((((((((s0_210,
                                                                                                                                       s_203),
                                                                                                                                      s0_204),
                                                                                                                                     s0_205),
                                                                                                                                    s0_206),
                                                                                                                                   s0_207),
                                                                                                                                  s0_208),
                                                                                                                                 s0_209),
                                                                                                                                s0_210),
                                                                                                                               s0_211),
                                                                                                                              s0_212))
putOutputK = \x_213 -> K (\s_214 -> \s0_215 -> \s0_216 -> \s0_217 -> \s0_218 -> \s0_219 -> \s0_220 -> \s0_221 -> \s0_222 -> \s0_223 -> (((((((((((),
                                                                                                                                                 s_214),
                                                                                                                                                s0_215),
                                                                                                                                               s0_216),
                                                                                                                                              s0_217),
                                                                                                                                             s0_218),
                                                                                                                                            s0_219),
                                                                                                                                           s0_220),
                                                                                                                                          x_213),
                                                                                                                                         s0_222),
                                                                                                                                        s0_223))
updateOutputK = \f_224 -> getOutputK >>= (\s_225 -> putOutputK (f_224 s_225) >> getOutputK)
getLocalDataK = K (\s_226 -> \s0_227 -> \s0_228 -> \s0_229 -> \s0_230 -> \s0_231 -> \s0_232 -> \s0_233 -> \s0_234 -> \s0_235 -> ((((((((((s0_234,
                                                                                                                                          s_226),
                                                                                                                                         s0_227),
                                                                                                                                        s0_228),
                                                                                                                                       s0_229),
                                                                                                                                      s0_230),
                                                                                                                                     s0_231),
                                                                                                                                    s0_232),
                                                                                                                                   s0_233),
                                                                                                                                  s0_234),
                                                                                                                                 s0_235))
putLocalDataK = \x_236 -> K (\s_237 -> \s0_238 -> \s0_239 -> \s0_240 -> \s0_241 -> \s0_242 -> \s0_243 -> \s0_244 -> \s0_245 -> \s0_246 -> (((((((((((),
                                                                                                                                                    s_237),
                                                                                                                                                   s0_238),
                                                                                                                                                  s0_239),
                                                                                                                                                 s0_240),
                                                                                                                                                s0_241),
                                                                                                                                               s0_242),
                                                                                                                                              s0_243),
                                                                                                                                             s0_244),
                                                                                                                                            x_236),
                                                                                                                                           s0_246))
updateLocalDataK = \f_247 -> getLocalDataK >>= (\s_248 -> putLocalDataK (f_247 s_248) >> getLocalDataK)
getMemK = K (\s_249 -> \s0_250 -> \s0_251 -> \s0_252 -> \s0_253 -> \s0_254 -> \s0_255 -> \s0_256 -> \s0_257 -> \s0_258 -> ((((((((((s0_258,
                                                                                                                                    s_249),
                                                                                                                                   s0_250),
                                                                                                                                  s0_251),
                                                                                                                                 s0_252),
                                                                                                                                s0_253),
                                                                                                                               s0_254),
                                                                                                                              s0_255),
                                                                                                                             s0_256),
                                                                                                                            s0_257),
                                                                                                                           s0_258))
putMemK = \x_259 -> K (\s_260 -> \s0_261 -> \s0_262 -> \s0_263 -> \s0_264 -> \s0_265 -> \s0_266 -> \s0_267 -> \s0_268 -> \s0_269 -> (((((((((((),
                                                                                                                                              s_260),
                                                                                                                                             s0_261),
                                                                                                                                            s0_262),
                                                                                                                                           s0_263),
                                                                                                                                          s0_264),
                                                                                                                                         s0_265),
                                                                                                                                        s0_266),
                                                                                                                                       s0_267),
                                                                                                                                      s0_268),
                                                                                                                                     x_259))
updateMemK = \f_270 -> getMemK >>= (\s_271 -> putMemK (f_270 s_271) >> getMemK)
runK = \x_272 -> \q_273 q_274 q_275 q_276 q_277 q_278 q_279 q_280 q_281 q_282 -> (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . id)))))))))) (deK x_272 q_273 q_274 q_275 q_276 q_277 q_278 q_279 q_280 q_281 q_282)
data R a_283 = DoneR a_283 | PauseR (K (R a_283))
instance Prelude.Monad R
    where (>>=) (DoneR v_284) f_285 = f_285 v_284
          (>>=) (PauseR r_286) f_287 = PauseR (r_286 >>= (\k_288 -> return (k_288 >>= f_287)))
          return = DoneR
stepR x_289 = PauseR (x_289 >>= (return . DoneR))
