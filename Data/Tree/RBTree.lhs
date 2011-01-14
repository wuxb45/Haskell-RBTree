  Module : RBTree
  Author : Wu Xingbo

  Copyright (c) 2010 Wu Xingbo (wuxb45@gmail.com)
  New BSD License (see http://www.opensource.org/licenses/bsd-license.php)

> module Data.Tree.RBTree 
> (Color, RBTree, emptyRB,
>  insert, insertOrd, insertOrdList, 
>  remove, removeOrd, removeOrdList,
>  search, searchOrd,
>  vD, vR
> )
> where

> import Control.Monad(liftM2)

  Basic RBTree Structures

> data Color = Red | Black deriving (Eq)

> data RBTree a = Node Color a (RBTree a) (RBTree a)
>               | Leaf

  RBTree in a 'Zip' mode.
  Current Node can start from any node inside the tree, with a Path back to Root node.
  RBZip is equivalent to RBTree in Logic.
  All RBZip can be convert to a RBTree by Trace back to Root point.

> data Direction = ToLeft | ToRight deriving (Show,Eq)

> data Path a = Path Color a Direction (RBTree a)
>               deriving (Show)

> data RBZip a = RBZip (RBTree a) [Path a]
>                deriving (Show)

  Simply show tree in (), hard to read but easy to parse

> instance Show a => Show (RBTree a) where
>     show (Node c v l r) = "(" ++ show l ++ show v ++ show c ++ show r ++ ")"
>     show Leaf = []

  Red node shows '*'

> instance Show Color where
>     show Red = "*"
>     show Black = ""

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

  Zip up.

> topMostZip :: RBZip a -> RBZip a

> topMostZip (RBZip s ((Path c v d s1):path)) =
>     topMostZip (RBZip (Node c v l r) path)
>     where (l,r) = case d of
>               ToLeft -> (s,s1)
>               ToRight -> (s1,s)
> topMostZip z = z

  Get the Leftmost non-leaf node from a Zip.

> leftmostZip :: RBZip a -> RBZip a

> leftmostZip this@(RBZip (Node _ _ Leaf _) _) = this
> leftmostZip (RBZip (Node c v l r) path) = leftmostZip (RBZip l ((Path c v ToLeft r):path))
> leftmostZip z = z

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
> insertRedZip f (RBZip (Node c v l r) path) new = case f new v of
>     LT -> insertRedZip f (RBZip l ((Path c v ToLeft r):path)) new
>     EQ -> insertRedZip f (RBZip l ((Path c v ToLeft r):path)) new
>     GT -> insertRedZip f (RBZip r ((Path c v ToRight l):path)) new

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
>           newD = setBlack d

> insertFixup (RBZip a@(Node Red va sal sar) ((Path Red vb db sb):(Path Black vc dc d):path)) =
>     RBZip newZ (newP:path)
>     where (newZ,newP) = case (dc,db) of 
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

> searchZip :: (a -> a -> Ordering) -> RBZip a -> a -> Maybe (RBZip a)

> searchZip _ (RBZip Leaf _) _ = Nothing
> searchZip f this@(RBZip (Node c v l r) path) vs = case f vs v of
>     LT -> searchZip f (RBZip l ((Path c v ToLeft r):path)) vs
>     GT -> searchZip f (RBZip r ((Path c v ToRight l):path)) vs
>     EQ -> Just this

  remove functions.
  If there is no 'a' in tree, tree will be returned unmodified.

> removeOrd :: (Ord a) => RBTree a -> a -> RBTree a

> removeOrd = remove compare

> removeOrdList :: (Ord a) => RBTree a -> [a] -> RBTree a

> removeOrdList = foldl removeOrd 

> remove :: (a -> a -> Ordering) -> RBTree a -> a -> RBTree a

> remove f t a = 
>     case searchZip f (toZip t) a of
>         Just z -> toTree . removeZip $ z
>         Nothing -> t

> removeZip :: RBZip a -> RBZip a

> removeZip z@(RBZip Leaf _) = z

  case 1: left null

> removeZip (RBZip (Node c _ Leaf r) path) = case c of --r may be Leaf
>     Red -> RBZip r path
>     Black -> removeFixup (RBZip r path)

  case 2: right null

> removeZip (RBZip (Node c _ l Leaf) path) = case c of
>     Red -> RBZip l path
>     Black -> removeFixup (RBZip l path)

  case 3: both not null

> removeZip (RBZip (Node c _ l r@(Node _ vr srl _)) path) = removeZip newX
>     where newX = leftmostZip (RBZip r ((Path c newV ToRight l):path))
>           newV = leftmostV vr srl

  fixup : 

> removeFixup :: RBZip a -> RBZip a

  endcase : 'a' may be Leaf!

> removeFixup (RBZip a@(Node Red _ _ _) path) = RBZip (setBlack a) path

  case 1: brother of x is Red

> removeFixup (RBZip a ((Path _ vb db (Node Red vd l r)):path)) =
>     removeFixup $ RBZip a ((Path Red vb db newW):(Path Black vd db newS):path)
>     where (newW,newS) = case db of
>               ToLeft -> (l,r)
>               ToRight -> (r,l)

  case 4: x's brother s is black, but s's outter child is Red
  c may be leaf

> removeFixup (RBZip a ((Path cb vb ToLeft (Node Black vd c e@(Node Red _ _ _))):path)) = 
>     removeFixup . topMostZip $ RBZip (Node cb vd (Node Black vb a c) (setBlack e)) path
> removeFixup (RBZip a ((Path cb vb ToRight (Node Black vd e@(Node Red _ _ _) c)):path)) = 
>     removeFixup . topMostZip $ RBZip (Node cb vd (setBlack e) (Node Black vb c a)) path

  case 3: x's brother s is black, but s's inner child is Red

> removeFixup (RBZip a ((Path cb vb ToLeft (Node Black vd (Node Red vc scl scr) e)):path)) = 
>     removeFixup $ RBZip a ((Path cb vb ToLeft (Node Black vc scl (Node Red vd scr e))):path)
> removeFixup (RBZip a ((Path cb vb ToRight (Node Black vd e (Node Red vc scl scr))):path)) = 
>     removeFixup $ RBZip a ((Path cb vb ToRight (Node Black vc (Node Red vd e scl) scr)):path)

  case 2: s's both children are not Red (Black or Leaf).

> removeFixup (RBZip a ((Path cb vb db d@(Node Black _ _ _)):path)) = 
>     removeFixup $ (RBZip (Node cb vb newL newR) path)
>     where (newL,newR) = case db of
>               ToLeft -> (a,d')
>               ToRight -> (d',a)
>           d' = setRed d

  any other case: set current node to black and return.

> removeFixup (RBZip a path) = RBZip (setBlack a) path

  Verification functions.

  vD : verify black-depth are all the same. 
  Return Just 'depth' on success, otherwise Nothing.

> vD :: RBTree a -> Maybe Int

> vD Leaf = Just 1
> vD (Node c _ l r) = 
>     case dl == dr of 
>         True -> liftM2 (+) inc dl
>         False -> Nothing
>     where dl = vD l
>           dr = vD r
>           inc = case c of
>               Red -> Just 0
>               Black -> Just 1

  vR : verify no 'red-red' pattern in x and x's parent

> vR :: RBTree a -> Bool

> vR Leaf = True
> vR (Node Black _ l r) = (vR l) && (vR r)
> vR (Node Red _ l r) = 
>     (cl /= Red) && (cr /= Red) && (vR l) && (vR r)
>     where cl = getColor l
>           cr = getColor r

