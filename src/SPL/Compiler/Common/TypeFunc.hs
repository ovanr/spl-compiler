{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module SPL.Compiler.Common.TypeFunc where

data HList (f :: k -> *) (xs :: [k]) where
    HNil :: HList f '[]
    (:+:) :: f x -> HList f xs -> HList f (x ': xs)

infixr 3 :+:

type family Snoc (xs :: [a]) (y :: a) :: [a] where
    Snoc '[] y = '[y]
    Snoc (x ': xs) y = x ': Snoc xs y

type family Append (xs :: [a]) (ys :: [a]) :: [a] where
    Append '[] ys = ys
    Append (x ': xs) ys = x ': Append xs ys

data Some1 (f :: k -> *) where
    Some1 :: f a -> Some1 f

data Some2 (f :: k -> z -> *) where
    Some2 :: f a b -> Some2 f

withSome1 :: Some1 f -> (forall x. f x -> c) -> c
withSome1 (Some1 x) f = f x

bindSome :: Some1 f -> (forall x. f x -> Some1 f) -> Some1 f
bindSome (Some1 x) f = f x

liftA2Some :: (forall x y. f x -> f y -> Some1 f) -> Some1 f -> Some1 f -> Some1 f
liftA2Some f (Some1 x) (Some1 y) = f x y

hListFromList :: [Some1 f] -> Some1 (HList f)
hListFromList [] = Some1 HNil
hListFromList (x:xs) =
    case (x, hListFromList xs) of
        (Some1 h, Some1 hs) -> Some1 (h :+: hs)

hListMap :: (forall x. f x -> Some1 g) -> HList f xs -> Some1 (HList g)
hListMap _ HNil = Some1 HNil
hListMap f (x :+: xs) =
    case (f x, hListMap f xs) of
        (Some1 fx, Some1 fxs) -> Some1 (fx :+: fxs)

hListMapM :: Monad m => (forall x. f x -> m (Some1 g)) -> HList f xs -> m (Some1 (HList g))
hListMapM _ HNil = pure (Some1 HNil)
hListMapM f (x :+: xs) = do
    Some1 fx <- f x
    Some1 fxs <- hListMapM f xs
    pure $ Some1 (fx :+: fxs)

hListMapToList :: (forall x. f x -> a) -> HList f xs -> [a]
hListMapToList f = map (\(Some1 x) -> f x) . hListToList

hListMapFromList :: (a -> Some1 g) -> [a] -> Some1 (HList g)
hListMapFromList f [] = Some1 HNil
hListMapFromList f (x:xs) = withSome1 (f x) $ \fx -> hListMapFromList f xs `bindSome` (Some1 . (:+:) fx) 

hListZip :: (forall x y. f x -> f y -> Some1 f) -> HList f xs -> HList f ys -> Some1 (HList f)
hListZip _ HNil _ = Some1 HNil
hListZip _ _ HNil = Some1 HNil
hListZip f (x :+: xs) (y :+: ys) =
    case (f x y, hListZip f xs ys ) of
        (Some1 fxy, Some1 fxsys) -> Some1 (fxy :+: fxsys)

hListZipM1 :: Monad m => (forall x y. f x -> f y -> m (f x)) -> HList f xs -> HList f ys -> m (HList f xs)
hListZipM1 _ HNil _ = pure HNil
hListZipM1 _ xs HNil = pure xs
hListZipM1 f (x :+: xs) (y :+: ys) = do
    fxy <- f x y
    fxsys <- hListZipM1 f xs ys
    pure (fxy :+: fxsys)

hListFoldl :: (forall x . acc -> f x -> acc) -> acc -> HList f xs -> acc
hListFoldl _ acc HNil = acc
hListFoldl f acc (x :+: xs) = hListFoldl f (f acc x) xs

hListToList :: HList f xs -> [Some1 f]
hListToList HNil = []
hListToList (x :+: xs) = Some1 x : hListToList xs

(+++) :: HList f xs -> HList f ys -> HList f (Append xs ys)
HNil +++ ys = ys
(x :+: xs) +++ ys = x :+: (xs +++ ys)

hListLength :: Num a => HList f xs -> a
hListLength HNil = 0
hListLength (_ :+: xs) = 1 + hListLength xs
