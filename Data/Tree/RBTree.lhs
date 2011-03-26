  Module : RBTree
  Author : Wu Xingbo

  Copyright (c) 2010, 2011 Wu Xingbo (wuxb45@gmail.com)
  New BSD License (see http://www.opensource.org/licenses/bsd-license.php)

> {-# LANGUAGE BangPatterns #-}

> module Data.Tree.RBTree
> (Color, RBTree, emptyRB,
>  insert, insertOrd, insertOrdList,
>  delete, deleteOrd, deleteOrdList,
>  search, searchOrd, searchFast,
>  vD, vR
> )
> where

> import Control.Monad(liftM2)

  Basic RBTree Structures

> data Color = Red | Black deriving (Eq)

> data RBTree a = Node Color a !(RBTree a) !(RBTree a)
>               | Leaf

  RBTree in a 'Zip' mode.
  Current Node can start from any node inside the tree, with a Path back to Root node.
  RBZip is equivalent to RBTree in Logic.
  All RBZip can be convert to a RBTree by Trace back to Root point.

> data Direction = ToLeft | ToRight deriving (Eq)

> data Path a = Path Color a Direction !(RBTree a)
>               deriving (Show)

> data RBZip a = RBZip !(RBTree a) ![Path a]
>                deriving (Show)

> data Interval a = Interval (RealOrd a, RealOrd a)

> data RealOrd a = PInfinity | NInfinity | RealValue a

  Simply show tree in (), hard to read but easy to parse

> instance Show a => Show (RBTree a) where
>     show (Node c v l r) = "(" ++ show l ++ show v ++ show c ++ show r ++ ")"
>     show Leaf = "."

  Red node shows '*'

> instance Show Color where
>     show Red = "*"
>     show Black = ""

> instance Show Direction where
>     show ToLeft = "L"
>     show ToRight = "R"

> instance Show a => Show (RealOrd a) where
>     show PInfinity = "+INF"
>     show NInfinity = "-INF"
>     show (RealValue a) = show a

> instance Show a => Show (Interval a) where
>     show (Interval (l, r)) = "[" ++ show l ++ ", " ++ show r ++ "]"

> emptyRB :: RBTree a

> emptyRB = Leaf

  Leaf is also Black

> getColor :: RBTree a -> Color

> getColor (Node c _ _ _) = c
> getColor Leaf = Black

  Set current RBTree's Root to Black/Red

> setBlack :: RBTree a -> RBTree a

> setBlack Leaf = Leaf
> setBlack (Node _ v l r) = Node Black v l r

> setRed :: RBTree a -> RBTree a

> setRed (Node _ v l r) = Node Red v l r
> setRed Leaf = Leaf -- never happen

  Conversion : RBTree <==> RBZip

> toZip :: RBTree a -> RBZip a

> toZip t = RBZip t []

> toTree :: RBZip a -> RBTree a

> toTree z = tree
>     where (RBZip tree _) = topMostZip z

> getValueZip :: RBZip a -> Maybe a
> getValueZip (RBZip Leaf _) = Nothing
> getValueZip (RBZip (Node _ v _ _) _) = Just v

  Zip up.

> topMostZip :: RBZip a -> RBZip a

> topMostZip (RBZip s ((Path c v d s1):path)) = case d of 
>         ToLeft -> topMostZip (RBZip (Node c v s s1) path)
>         ToRight -> topMostZip (RBZip (Node c v s1 s) path)
> topMostZip z = z

  Get the Leftmost non-leaf node from a Zip.

> leftMostZip :: RBZip a -> RBZip a

> leftMostZip this@(RBZip (Node _ _ Leaf _) _) = this
> leftMostZip (RBZip (Node c v l r) path) = leftMostZip (RBZip l ((Path c v ToLeft r):path))
> leftMostZip z = z --only when leaf itself from start over

> rightMostZip :: RBZip a -> RBZip a

> rightMostZip this@(RBZip (Node _ _ _ Leaf) _) = this
> rightMostZip (RBZip (Node c v l r) path) = rightMostZip (RBZip r ((Path c v ToRight l):path))
> rightMostZip z = z --leaf itself

> leftParentZip :: RBZip a -> RBZip a
> leftParentZip (RBZip l ((Path c v ToLeft r):path)) = leftParentZip (RBZip (Node c v l r) path)
> leftParentZip (RBZip r ((Path c v ToRight l):path)) = RBZip (Node c v l r) path
> leftParentZip (RBZip t []) = RBZip Leaf [] -- no such parent, return a empty zip

> rightParentZip :: RBZip a -> RBZip a
> rightParentZip (RBZip r ((Path c v ToRight l):path)) = rightParentZip (RBZip (Node c v l r) path)
> rightParentZip (RBZip l ((Path c v ToLeft r):path)) = RBZip (Node c v l r) path
> rightParentZip (RBZip t []) = RBZip Leaf [] -- no such parent, return a empty zip

  find predecessor/successor of a node/leaf

> predZip :: RBZip a -> RBZip a

> predZip (RBZip (Node c v l@(Node _ _ _ _) r) path) = rightMostZip (RBZip l ((Path c v ToLeft r):path))
> predZip z@(RBZip Leaf path) = case lp of
>   RBZip Leaf [] -> z -- itself
>   _ -> lp
>   where lp = leftParentZip z
> predZip z@(RBZip (Node c v l r) path) = case lp of
>   RBZip Leaf [] -> RBZip l ((Path c v ToLeft r):path)
>   _ -> lp
>   where lp = leftParentZip z

> succZip :: RBZip a -> RBZip a

> succZip (RBZip (Node c v l r@(Node _ _ _ _)) path) = leftMostZip (RBZip r ((Path c v ToRight l):path))
> succZip z@(RBZip Leaf path) = case lp of
>   RBZip Leaf [] -> z -- itself
>   _ -> lp
>   where lp = rightParentZip z
> succZip z@(RBZip (Node c v l r) path) = case lp of
>   RBZip Leaf [] -> RBZip r ((Path c v ToRight l):path)
>   _ -> lp
>   where lp = rightParentZip z

  Get the Leftmost non-leaf node's value from a Zip.
  param 1 : current node's value.
  param 2 : current node's left child.

> leftmostV :: a -> RBTree a -> a

> leftmostV v Leaf = v
> leftmostV _ (Node _ vl l _) = leftmostV vl l

  Insertion functions. x will be in left of y if x equals to y and y has already in the tree.

  Insert 'Ord' things.

> insertOrd :: (Ord a) => RBTree a -> a -> RBTree a

> insertOrd = insert compare

  Insert a bunch of 'Ord' things.

> insertOrdList :: (Ord a) => RBTree a -> [a] -> RBTree a

> insertOrdList = foldl insertOrd

  Insert anything.
  you have to provide a compare function.

> insert :: (a -> a -> Ordering) -> RBTree a -> a ->RBTree a

> insert f t v = setBlack . toTree . insertFixup . (insertRedZip f (toZip t)) $ v

> insertRedZip :: (a -> a -> Ordering) -> RBZip a -> a -> RBZip a

> insertRedZip _ (RBZip Leaf path) v = RBZip (Node Red v Leaf Leaf) path
> insertRedZip f (RBZip (Node c v l r) path) new
>     | f new v == GT = insertRedZip f (RBZip r ((Path c v ToRight l):path)) new
>     | otherwise     = insertRedZip f (RBZip l ((Path c v ToLeft r):path)) new

  insertFixup:
  a : current node
  b : parent of a
  c : parent of b
  d : brother of b
  vx : value of x
  dx : direction of x
  sx : sub-tree of x in the path
  sxy : sub-tree of x in y side

> insertFixup :: RBZip a -> RBZip a

> insertFixup (RBZip a@(Node Red _ _ _) ((Path Red vb db sb):(Path Black vc dc d@(Node Red _ _ _)):path)) =
>     insertFixup (RBZip newC path)
>     where newC = Node Red vc newCL newCR
>           (newCL,newCR) = case dc of
>               ToLeft -> (newB,newD)
>               ToRight -> (newD,newB)
>           newB = Node Black vb newBL newBR
>           (newBL,newBR) = case db of
>               ToLeft -> (a,sb)
>               ToRight -> (sb,a)
>           !newD = setBlack d

> insertFixup (RBZip a@(Node Red va sal sar) ((Path Red vb db sb):(Path Black vc dc d):path)) =
>     RBZip newZ (newP:path)
>     where (newZ, newP) = case (dc,db) of 
>               (ToLeft,ToLeft) -> (a,Path Black vb dc (Node Red vc sb d))
>               (ToLeft,ToRight) -> (Node Red vb sb sal, Path Black va dc (Node Red vc sar d))
>               (ToRight,ToLeft) -> (Node Red vb sar sb, Path Black va dc (Node Red vc d sal))
>               (ToRight,ToRight) -> (a,Path Black vb dc (Node Red vc d sb))

> insertFixup t = t

  Search functions. return 'Just result' on success, otherwise Nothing.

> searchOrd :: (Ord a) => RBTree a -> a -> Maybe a

> searchOrd = search compare

> search :: (a -> a -> Ordering) -> RBTree a -> a -> Maybe a

> search f t v = case rZip of
>     Just (RBZip (Node _ v' _ _) _) -> Just v'
>     _ -> Nothing
>     where rZip = searchZip f (toZip t) v

> searchFast :: (a -> a -> Ordering) -> RBTree a -> a -> Maybe a

> searchFast f (Node _ v l r) vs = case f vs v of
>     LT -> searchFast f l vs
>     GT -> searchFast f r vs
>     EQ -> Just v
> searchFast _ Leaf _ = Nothing

> searchZip :: (a -> a -> Ordering) -> RBZip a -> a -> Maybe (RBZip a)

> searchZip _ (RBZip Leaf _) _ = Nothing
> searchZip f this@(RBZip (Node c v l r) path) vs = case f vs v of
>     LT -> searchZip f (RBZip l ((Path c v ToLeft r):path)) vs
>     GT -> searchZip f (RBZip r ((Path c v ToRight l):path)) vs
>     EQ -> Just this

  searchZipTrace : always returns the current point that the search stops.
  returns a Zip-Node on equal, otherwise a Zip-Leaf

> searchZipTrace :: (a -> a -> Ordering) -> RBZip a -> a -> RBZip a
> searchZipTrace _ zip@(RBZip Leaf _) _ = zip
> searchZipTrace f this@(RBZip (Node c v l r) path) vs = case f vs v of
>     LT -> searchZipTrace f (RBZip l ((Path c v ToLeft r):path)) vs
>     GT -> searchZipTrace f (RBZip r ((Path c v ToRight l):path)) vs
>     EQ -> this

> searchIntervalOrd :: (Ord a) => RBTree a -> a -> Interval a
> searchIntervalOrd t a = searchInterval compare t a

> searchInterval :: (a -> a -> Ordering) -> RBTree a -> a -> Interval a
> searchInterval f t a = case r of
>     RBZip Leaf _ -> Interval (toNRealOrd (predZip r), toPRealOrd (succZip r))
>     _ -> Interval (toNRealOrd r, toPRealOrd r)
>     where r = searchZipTrace f (toZip t) a
>           toNRealOrd (RBZip Leaf _) = NInfinity
>           toNRealOrd (RBZip (Node _ v _ _) _) = RealValue v
>           toPRealOrd (RBZip Leaf _) = PInfinity
>           toPRealOrd (RBZip (Node _ v _ _) _) = RealValue v

  delete functions.
  If there is no 'a' in tree, tree will be returned unmodified.

> deleteOrd :: (Ord a) => RBTree a -> a -> RBTree a

> deleteOrd = delete compare

> deleteOrdList :: (Ord a) => RBTree a -> [a] -> RBTree a

> deleteOrdList = foldl deleteOrd 

> delete :: (a -> a -> Ordering) -> RBTree a -> a -> RBTree a

> delete f t a = 
>     case searchZip f (toZip t) a of
>         Just z -> toTree . deleteZip $ z
>         Nothing -> t

> deleteZip :: RBZip a -> RBZip a

> deleteZip z@(RBZip Leaf _) = z

  case 1: left null

> deleteZip (RBZip (Node c _ Leaf r) path) = case c of --r may be Leaf
>     Red -> RBZip r path
>     Black -> deleteFixup (RBZip r path)

  case 2: right null

> deleteZip (RBZip (Node c _ l Leaf) path) = case c of
>     Red -> RBZip l path
>     Black -> deleteFixup (RBZip l path)

  case 3: both not null

> deleteZip (RBZip (Node c _ l r@(Node _ vr srl _)) path) = deleteZip newX
>     where !newX = leftMostZip (RBZip r ((Path c newV ToRight l):path))
>           !newV = leftmostV vr srl

  fixup : 

> deleteFixup :: RBZip a -> RBZip a

  endcase : 'a' may be Leaf!

> deleteFixup (RBZip a@(Node Red _ _ _) path) = RBZip (setBlack a) path

  case 1: brother of x is Red

> deleteFixup (RBZip a ((Path _ vb db (Node Red vd l r)):path)) =
>     deleteFixup $ RBZip a ((Path Red vb db newW):(Path Black vd db newS):path)
>     where (!newW, !newS) = case db of
>               ToLeft -> (l,r)
>               ToRight -> (r,l)

  case 4: x's brother s is black, but s's outter child is Red
  c may be leaf

> deleteFixup (RBZip a ((Path cb vb ToLeft (Node Black vd c e@(Node Red _ _ _))):path)) = 
>     deleteFixup . topMostZip $ RBZip (Node cb vd (Node Black vb a c) (setBlack e)) path
> deleteFixup (RBZip a ((Path cb vb ToRight (Node Black vd e@(Node Red _ _ _) c)):path)) = 
>     deleteFixup . topMostZip $ RBZip (Node cb vd (setBlack e) (Node Black vb c a)) path

  case 3: x's brother s is black, but s's inner child is Red

> deleteFixup (RBZip a ((Path cb vb ToLeft (Node Black vd (Node Red vc scl scr) e)):path)) = 
>     deleteFixup $ RBZip a ((Path cb vb ToLeft (Node Black vc scl (Node Red vd scr e))):path)
> deleteFixup (RBZip a ((Path cb vb ToRight (Node Black vd e (Node Red vc scl scr))):path)) = 
>     deleteFixup $ RBZip a ((Path cb vb ToRight (Node Black vc (Node Red vd e scl) scr)):path)

  case 2: s's both children are not Red (Black or Leaf).

> deleteFixup (RBZip a ((Path cb vb db d@(Node Black _ _ _)):path)) = 
>     deleteFixup $ (RBZip (Node cb vb newL newR) path)
>     where (!newL, !newR) = case db of
>               ToLeft -> (a,d')
>               ToRight -> (d',a)
>           !d' = setRed d

  any other case: set current node to black and return.

> deleteFixup (RBZip a path) = RBZip (setBlack a) path

  Verification functions.

  vD : verify black-depth are all the same. 
  Return Just 'depth' on success, otherwise Nothing.

> vD :: RBTree a -> Maybe Int

> vD Leaf = Just 1
> vD (Node c _ l r) = 
>     case dl == dr of 
>         True -> liftM2 (+) inc dl
>         False -> Nothing
>     where !dl = vD l
>           !dr = vD r
>           !inc = case c of
>               Red -> Just 0
>               Black -> Just 1

  vR : verify no 'red-red' pattern in x and x's parent

> vR :: RBTree a -> Bool

> vR Leaf = True
> vR (Node Black _ l r) = (vR l) && (vR r)
> vR (Node Red _ l r) = 
>     (cl /= Red) && (cr /= Red) && (vR l) && (vR r)
>     where !cl = getColor l
>           !cr = getColor r

