--
-- this is ~/cheapthreads/ctc_working/CT-1.0/TestPrograms/Test2.hs
--
-- this is the part where the parser eats its own vomit,
-- and hopefully doesn't choke
--
-- 2010.01.06
--
-- Schulz
--

main z =
step( get G >>= \x ->
put G ((x + 1)) >>= \y ->
return (f( y( z)))) >>
return (())
