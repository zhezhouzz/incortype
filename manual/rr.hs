{-@ LIQUID "--notermination" @-}
{-@ LIQUID "--reflection" @-}
-- import Language.Haskell.Liquid.Prelude  (liquidAssert)
import Language.Haskell.Liquid.ProofCombinators 
  
{-@ reflect mem @-}
{-@ mem :: s:[Int] -> x:Int -> Bool @-}
mem :: [Int] -> Int -> Bool
mem [] _ = False
mem (h : t) x =
    if x == h then True else mem t x
    
{-@ reflect rep_set @-}
{-@ rep_set :: s:[Int] -> Bool @-}
rep_set :: [Int] -> Bool
rep_set [] = True
rep_set (h : t) =
    if mem t h then False else rep_set t

{-@ reflect insert_v1 @-}
{-@ insert_v1 :: s:[Int]-> x:Int -> [Int] @-}
insert_v1 :: [Int] -> Int -> [Int]
insert_v1 [] x = [x]
insert_v1 (h : t) x =
    if x == h then (h : t) else h : (insert_v1 t x)
 
 {-@ insert_v1_correct :: s:{v:[Int] | rep_set v} -> x:Int -> {rep_set (insert_v1 s x)} @-}
insert_v1_correct [] x =
    rep_set (insert_v1 [] x)
    ==. rep_set [x]
    *** QED
insert_v1_correct (h : t) x
    | h == x
    = rep_set (insert_v1 (h : t) x)
    ==. rep_set (h : t)
    *** QED
    | otherwise
    *** QED

