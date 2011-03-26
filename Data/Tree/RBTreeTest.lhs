
> module Data.Tree.RBTreeTest where

> import Data.List(foldl')
> import Data.Tree.RBTree

> testRB :: String
> testRB = vA emptyRB ts
>    where ts = ([100..1065]++[1..80]++[200..220]):
>            ([5..70] ++ [200..215]++[105..155]):
>            ([8888..99999]++[5..70]++[700..1900]):
>            [[9374..43388]++[73333..87777]] :: [[Int]]

> vA :: Ord a => RBTree a -> [[a]] -> String
> vA t (i:r:xs) = 
>     show (vD ti) ++ show (vR ti) 
>       ++ " " ++ show (vD tr) ++ show (vR tr) 
>       ++ " " ++ (vA tr xs)
>     where ti = foldl' insertOrd t i
>           tr = foldl' deleteOrd ti r
> vA _ _ = ""

