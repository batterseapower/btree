{-# LANGUAGE GADTs, EmptyDataDecls, ExistentialQuantification #-}
module BTree where

import Prelude hiding (elem)
import Data.Foldable hiding (elem, foldr)
import Data.Monoid

data Z
data S a

-- 2/3 B-tree
data BT d a where
    Nil     :: BT Z a
    Branch2 :: BT d a -> a -> BT d a                -> BT (S d) a
    Branch3 :: BT d a -> a -> BT d a -> a -> BT d a -> BT (S d) a

instance Foldable (BT d) where
    foldMap _ Nil = mempty
    foldMap f (Branch2 ys0 y1 ys2) = foldMap f ys0 `mappend` f y1 `mappend` foldMap f ys2
    foldMap f (Branch3 ys0 y1 ys2 y3 ys4) = foldMap f ys0 `mappend` f y1 `mappend` foldMap f ys2 `mappend` f y3 `mappend` foldMap f ys4

instance Show a => Show (BT d a) where
    show bt = "fromList " ++ show (toList bt)

elem :: Ord a => a -> BT d a -> Bool
elem _ Nil = False
elem x (Branch2 ys0 y1 ys2) = case x `compare` y1 of
    EQ -> True
    LT -> elem x ys0
    GT -> elem x ys2
elem x (Branch3 ys0 y1 ys2 y3 ys4) = case x `compare` y1 of
    EQ -> True
    LT -> elem x ys0
    GT -> case x `compare` y3 of
        EQ -> True
        LT -> elem x ys2
        GT -> elem x ys4

insertTop :: Ord a => a -> BT d a -> Either (BT (S d) a) (BT d a)
insertTop x bt = case insert x bt of
    Overflow l x' r -> Left (Branch2 l x' r)
    InsertFits bt'  -> Right bt'

data InsertResult d a where
    Overflow   :: BT d a -> a -> BT d a -> InsertResult d a
    InsertFits :: BT d a -> InsertResult d a

insert :: Ord a => a -> BT d a -> InsertResult d a
insert x Nil = Overflow Nil x Nil
insert x br@(Branch2 ys0 y1 ys2) = InsertFits (case x `compare` y1 of
    EQ -> br
    LT -> case insert x ys0 of
        InsertFits ys0'       -> Branch2 ys0' y1 ys2
        Overflow ys0l x' ys0r -> Branch3 ys0l x' ys0r y1 ys2
    GT -> case insert x ys2 of
        InsertFits ys2'       -> Branch2 ys0 y1 ys2'
        Overflow ys2l x' ys2r -> Branch3 ys0 y1 ys2l x' ys2r)
insert x br@(Branch3 ys0 y1 ys2 y3 ys4) = case x `compare` y1 of
    EQ -> InsertFits br
    LT -> case insert x ys0 of
        InsertFits ys0'       -> InsertFits (Branch3 ys0' y1 ys2 y3 ys4)
        Overflow ys0l x' ys0r -> branch4 ys0l x' ys0r y1 ys2 y3 ys4
    GT -> case x `compare` y3 of
        EQ -> InsertFits br
        LT -> case insert x ys2 of
            InsertFits ys2'       -> InsertFits (Branch3 ys0 y1 ys2' y3 ys4)
            Overflow ys2l x' ys2r -> branch4 ys0 y1 ys2l x' ys2r y3 ys4
        GT -> case insert x ys4 of
            InsertFits ys4'       -> InsertFits (Branch3 ys0 y1 ys2 y3 ys4')
            Overflow ys4l x' ys4r -> branch4 ys0 y1 ys2 y3 ys4l x' ys4r

branch4 :: BT d a -> a -> BT d a -> a -> BT d a -> a -> BT d a -> InsertResult (S d) a
branch4 ys0 y1 ys2 y3 ys4 y5 ys6 = Overflow (Branch2 ys0 y1 ys2) y3 (Branch2 ys4 y5 ys6)

data DeleteResult d a where
    Underflow  :: BT d a -> BT d a -> DeleteResult (S d) a
    DeleteFits :: BT d a -> DeleteResult d a

delete :: Ord a => a -> BT d a -> DeleteResult d a
delete _ Nil = DeleteFits Nil
delete x (Branch2 ys0 y1 ys2) = case x `compare` y1 of
    EQ -> Underflow ys0 ys2
    LT -> case delete x ys0 of
        DeleteFits ys0'     -> DeleteFits (Branch2 ys0' y1 ys2)
        Underflow ys0l ys0r -> Underflow (rot0 ys0l ys0r y1) ys2
    GT -> case delete x ys2 of
        DeleteFits ys2'     -> DeleteFits (Branch2 ys0 y1 ys2')
        Underflow ys2l ys2r -> Underflow ys0 (rot1 y1 ys2l ys2r)
delete x (Branch3 ys0 y1 ys2 y3 ys4) = case x `compare` y1 of
    EQ -> f2 ys0 ys2 y3 ys4
    LT -> case delete x ys0 of
        DeleteFits ys0'     -> DeleteFits (Branch3 ys0' y1 ys2 y3 ys4)
        Underflow ys0l ys0r -> f2 (rot0 ys0l ys0r y1) ys2 y3 ys4
    GT -> case x `compare` y3 of
        EQ -> f3 ys0 y1 ys2 ys4
        LT -> case delete x ys2 of
            DeleteFits ys2'     -> DeleteFits (Branch3 ys0 y1 ys2' y3 ys4)
            Underflow ys2l ys2r -> f3 ys0 y1 (rot0 ys2l ys2r y3) ys4 
        GT -> case delete x ys4 of
            DeleteFits ys4'     -> DeleteFits (Branch3 ys0 y1 ys2 y3 ys4')
            Underflow ys4l ys4r -> f3 ys0 y1 ys2 (rot1 y3 ys4l ys4r)

rot0 :: BT d a -> BT d a -> a -> BT (S d) a
rot0 ys0 ys1 y2 = uncurry (Branch2 ys0) (shuffle0 ys1 y2)

shuffle0 :: BT d a -> a -> (a, BT d a)
shuffle0 Nil                  y0 = (y0, Nil)
shuffle0 (Branch2 ys0 y1 ys2) y3 = (y0, Branch2 ys1 y2 ys3)
  where (y2, ys3) = shuffle0 ys2 y3
        (y0, ys1) = shuffle0 ys0 y1  
shuffle0 (Branch3 ys0 y1 ys2 y3 ys4) y5 = (y0, Branch3 ys1 y2 ys3 y4 ys5)
  where (y4, ys5) = shuffle0 ys4 y5
        (y2, ys3) = shuffle0 ys2 y3
        (y0, ys1) = shuffle0 ys0 y1


rot1 :: a -> BT d a -> BT d a -> BT (S d) a
rot1 y0 ys1 ys2 = uncurry Branch2 (shuffle1 y0 ys1) ys2

shuffle1 :: a -> BT d a -> (BT d a, a)
shuffle1 y0 Nil = (Nil, y0)
shuffle1 y0 (Branch2 ys1 y2 ys3) = (Branch2 ys0 y1 ys2, y3)
  where (ys0, y1) = shuffle1 y0 ys1
        (ys2, y3) = shuffle1 y2 ys3
shuffle1 y0 (Branch3 ys1 y2 ys3 y4 ys5) = (Branch3 ys0 y1 ys2 y3 ys4, y5)
  where (ys0, y1) = shuffle1 y0 ys1
        (ys2, y3) = shuffle1 y2 ys3
        (ys4, y5) = shuffle1 y4 ys5


f2 :: BT d a -> BT d a -> a -> BT d a -> DeleteResult (S d) a
f2 = undefined

f3 :: BT d a -> a -> BT d a -> BT d a -> DeleteResult (S d) a
f3 Nil y0 Nil Nil                                                    = DeleteFits (Branch2 Nil y0 Nil)
f3 (Branch2 ys0 y1 ys2) y3 (Branch2 ys4 y5 ys6) (Branch2 ys7 y8 ys9) = Underflow (Branch3 ys0 y1 ys2 y3 ys4) (uncurry Branch3 (shuffle1 y5 ys6) ys7 y8 ys9)
--f3 (Branch3 ys0 y1 ys2 y3 ys4) y5 ys6 ys7 = DeleteFits (Branch3 (Branch2 ys0 y1 ys2) y3 )
f3 _ _ _ _ = undefined

data SomeBT a = forall d. SomeBT (BT d a)

instance Foldable SomeBT where
    foldMap f (SomeBT bt) = foldMap f bt

instance Show a => Show (SomeBT a) where
    show (SomeBT bt) = show bt

empty' :: SomeBT a
empty' = SomeBT Nil

fromList' :: Ord a => [a] -> SomeBT a
fromList' = foldr insert' empty'

insert' :: Ord a => a -> SomeBT a -> SomeBT a
insert' x (SomeBT bt) = either SomeBT SomeBT (insertTop x bt)

elem' :: Ord a => a -> SomeBT a -> Bool
elem' x (SomeBT bt) = elem x bt
