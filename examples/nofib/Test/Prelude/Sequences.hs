{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Test.Prelude.Sequences (

  test_sequences

) where

import Prelude                                                  as P
import Data.Label
import Data.Maybe
import Data.Typeable
import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck                                          hiding ( generate, collect, elements )
import qualified Test.QuickCheck                                as T

import Config
import QuickCheck.Arbitrary.Array                               ( arbitrarySegments, shrinkSegments )
import Data.Array.Accelerate.Examples.Internal
import Data.Array.Accelerate                                    as A
import Data.Array.Accelerate.Array.Sugar                        as Sugar


test_sequences :: Backend -> Config -> Test
test_sequences backend opt = testGroup "sequences" $ catMaybes
  [ testIntegralElt configInt8   (undefined :: Int8)
  , testIntegralElt configInt16  (undefined :: Int16)
  , testIntegralElt configInt32  (undefined :: Int32)
  , testIntegralElt configInt64  (undefined :: Int64)
  , testIntegralElt configWord8  (undefined :: Word8)
  , testIntegralElt configWord16 (undefined :: Word16)
  , testIntegralElt configWord32 (undefined :: Word32)
  , testIntegralElt configWord64 (undefined :: Word64)
  , testFloatingElt configFloat  (undefined :: Float)
  , testFloatingElt configDouble (undefined :: Double)
  , testLifted
  ]
  where
    testIntegralElt :: forall a. (P.Integral a, P.Bounded a, A.Num a, A.Ord a, A.Bounded a, Arbitrary a, Similar a) => (Config :-> Bool) -> a -> Maybe Test
    testIntegralElt ok _
      | P.not (get ok opt)  = Nothing
      | otherwise           = Just $ testGroup (show (typeOf (undefined::a)))
          [ testGroup "id"
              [ testProperty "DIM1" (test_id :: Array DIM1 a -> Property)
              , testProperty "DIM2" (test_id :: Array DIM2 a -> Property)
              , testProperty "DIM3" (test_id :: Array DIM3 a -> Property)
              ]
          , testProperty "maxSum"   (test_maxSum  :: Vector a -> Property)
          , testProperty "scatter"  (test_scatter :: Vector a -> Vector (Int,a) -> Property)
          , testProperty "append"   (test_append  :: Array DIM2 a -> Array DIM2 a -> Property)
          , testGroup "subarrays"
              [ testProperty "DIM1" (test_subarrays subarrays1Ref :: Array DIM1 a -> Property)
              , testProperty "DIM2" (test_subarrays subarrays2Ref :: Array DIM2 a -> Property)
              ]
          , testGroup "fold"
              [ testProperty "DIM2" (test_fold :: Array DIM2 a -> Property)
              , testProperty "DIM3" (test_fold :: Array DIM3 a -> Property)
              ]
          ]
      where
        test_maxSum xs = run1 backend sumMaxSequence xs ~?= sumMaxSequenceRef xs

    testFloatingElt :: forall a. (P.Floating a, A.Floating a, A.FromIntegral Int a, Arbitrary a, Similar a) => (Config :-> Bool) -> a -> Maybe Test
    testFloatingElt ok _
      | P.not (get ok opt)  = Nothing
      | otherwise           = Just $ testGroup (show (typeOf (undefined::a)))
          [ testGroup "id"
              [ testProperty "DIM1" (test_id :: Array DIM1 a -> Property)
              , testProperty "DIM2" (test_id :: Array DIM2 a -> Property)
              , testProperty "DIM3" (test_id :: Array DIM3 a -> Property)
              ]
          , testProperty "logSum"   test_logSum
          , testProperty "scatter"  (test_scatter :: Vector a -> Vector (Int,a) -> Property)
          , testProperty "append"   (test_append  :: Array DIM2 a -> Array DIM2 a -> Property)
          , testGroup "subarrays"
              [ testProperty "DIM1" (test_subarrays subarrays1Ref :: Array DIM1 a -> Property)
              , testProperty "DIM2" (test_subarrays subarrays2Ref :: Array DIM2 a -> Property)
              ]
          , testGroup "fold"
              [ testProperty "DIM2" (test_fold :: Array DIM2 a -> Property)
              , testProperty "DIM3" (test_fold :: Array DIM3 a -> Property)
              ]
          ]
      where
        test_logSum (NonNegative n) = run1 backend logsum (singleton n) ~?= (logsumRef n :: Scalar a)

    -- Apparently @robeverest doesn't think these should be tested against on types...
    testLifted :: Maybe Test
    testLifted = Just $ testGroup "lifted"
      [ testGroup "enumeration"
          [ testProperty "simple"     test_enum
          , testProperty "increasing" test_enumInc
          , testProperty "irregular"  test_enumIrr
          ]
      , testGroup "irregular"
          [ testProperty "append"     test_appendIrr
          , testProperty "fold"       test_foldIrr
          , testProperty "weird"      test_weird      -- TLM: @robeverest this needs an actual name
          ]
      ]

    singleton x = fromList Z [x]

    -- Tests
    test_id :: (Similar e, Elt e, P.Eq sh, Slice sh, Shape sh) => Array (sh :. Int) e -> Property
    test_id xs = normalise (run1 backend idSequence xs) ~?= normalise (idSequenceRef xs)

    test_scatter :: (Similar e, P.Num e, A.Num e) => Vector e -> Vector (Int,e) -> Property
    test_scatter xs ys
      =   arraySize (arrayShape xs) P.> 0
      ==> run2 backend scatterSequence xs ys ~?= scatterSequenceRef xs ys

    test_subarrays :: (Similar e, P.Eq sh, Shape sh, sh :<= DIM2, Elt e) => (sh -> Array sh e -> Array (sh:.Int) e) -> Array sh e -> Property
    test_subarrays ref xs
      =   arraySize (arrayShape xs) P.> 0
      ==> forAll (subshapesOf (arrayShape xs)) $ \sh ->
            normalise (run backend (collect . tabulate $ subarrays (constant sh) xs))
        ~?= normalise (ref sh xs)

    test_enum    (NonNegative n) (NonNegative m) = run2 backend enumeration (singleton n) (singleton m) ~?= enumerationRef n m
    test_enumInc (NonNegative n)                 = run1 backend enumerationIncreasing (singleton n)     ~?= enumerationIncreasingRef n
    test_enumIrr =
      forAllShrink arbitrarySegments shrinkSegments $ \segs ->
        run1 backend enumerationIrregular segs ~?= enumerationIrregularRef segs

    test_append :: (Similar e, Elt e) => Array DIM2 e -> Array DIM2 e -> Property
    test_append xs ys = run2 backend append xs ys ~?= appendRef xs ys
    test_appendIrr (NonNegative x) (NonNegative y) = run2 backend appendIrregular (singleton x) (singleton y) ~?= appendIrregularRef x y

    test_fold :: (Similar e, Shape sh, P.Eq sh, P.Num e, A.Num e) => Array (sh:.Int:.Int) e -> Property
    test_fold xs = normalise (run1 backend regularFold xs) ~?= normalise (regularFoldRef xs)
    test_foldIrr (NonNegative n) = run1 backend irregularFold (singleton n) ~?= irregularFoldRef n

    test_weird (NonNegative n) = run1 backend irregular (singleton n) ~?= irregularRef n



-- We need to introduce a normal form for arrays where any arrays of size zero
-- are coerced into an array with the empty shape. e.g. An array of shape
-- (Z:.2:.0) becomes and array of shape (Z:.0:.0)
--
normalise :: forall sh e. Shape sh => Array sh e -> Array sh e
normalise arr@(Array sh adata) = Array sh' adata
  where
    sh' | arraySize (arrayShape arr) P.== 0 = fromElt (empty :: sh)
        | otherwise                         = sh

iota :: Acc (Scalar Int) -> Acc (Vector Int)
iota n = generate (index1 (the n)) unindex1

-- iotaChunk :: Int -> Int -> Acc (Array (Z :. Int :. Int) Int)
-- iotaChunk n b = reshape (constant (Z :. b :. n)) $ generate (index1 (constant (n * b))) unindex1

idSequence
    :: forall sh a. (Shape sh, Slice sh, Elt a)
    => Acc (Array (sh :. Int) a)
    -> Acc (Array (sh :. Int) a)
idSequence xs
  = collect
  . tabulate
  $ toSeqOuter xs

idSequenceRef :: (Shape sh, Elt a) => Array (sh :. Int) a -> Array (sh :. Int) a
idSequenceRef = id

sumMaxSequence :: (A.Num a, A.Ord a, A.Bounded a) => Acc (Vector a) -> Acc (Scalar a, Scalar a)
sumMaxSequence xs = collect $
  let xs' = toSeqInner xs
  in  lift ( foldSeqE (+) 0 xs'
           , foldSeqE A.max minBound xs'
           )

sumMaxSequenceRef :: (Elt a, P.Ord a, P.Bounded a, P.Num a) => Vector a -> (Scalar a, Scalar a)
sumMaxSequenceRef xs =
  ( fromList Z . (:[]) . P.sum                    . toList $ xs
  , fromList Z . (:[]) . P.foldl (P.max) minBound . toList $ xs
  )

scatterSequence :: A.Num a => Acc (Vector a) -> Acc (Vector (Int, a)) -> Acc (Vector a)
scatterSequence vec vec_upd
  = collect
  $ foldSeqFlatten f vec
  $ toSeqInner vec_upd
  where
    f xs' _ upd =
      let (to, ys) = A.unzip upd
      in permute (+) xs' (index1 . (`mod` A.size vec) . (to A.!)) ys

scatterSequenceRef :: (Elt a, P.Num a) => Vector a -> Vector (Int, a) -> Vector a
scatterSequenceRef vec vec_upd =
  let
      xs           = toList vec
      updates      = toList vec_upd
      n            = P.length xs
      ys           = P.foldl f xs updates
      f xs' (i, x) = [ if j P.== i `P.mod` n then x P.+ y else y | (j, y) <- P.zip [0..] xs']
  in
  fromList (Z :. n) ys

logsum :: (A.Floating a, A.FromIntegral Int a) => Acc (Scalar Int) -> Acc (Scalar a)
logsum n = collect
  $ foldSeqE (+) 0.0
  $ mapSeq (A.map (log . A.fromIntegral . (+1)))
  $ toSeqInner (iota n)

logsumRef :: (Elt a, P.Floating a) => Int -> Scalar a
logsumRef n = fromList Z [P.sum [log (P.fromIntegral i) | i <- [1..n]]]

-- nestedSequence :: Int -> Int -> Acc (Vector Int)
-- nestedSequence n m = asnd . collect
--   $ fromSeq
--   $ mapSeq
--   (\ i -> collect
--           $ foldSeq (+) 0
--           $ mapSeq (A.zipWith (+) i)
--           $ toSeqInner (iota m)
--   )
--   $ toSeqInner (iota n)

-- nestedSequenceRef :: Int -> Int -> Vector Int
-- nestedSequenceRef n m = fromList (Z :. n) [P.sum [i + j | j <- [0..m-1]] | i <- [0..n-1]]
--
-- nestedIrregularSequence :: Int -> Acc (Vector Int)
-- nestedIrregularSequence n = asnd . collect
--   $ fromSeq
--   $ mapSeq
--   (\ i -> collect
--         $ foldSeq (+) 0
--         $ mapSeq (A.zipWith (+) i)
--         $ toSeqInner (iota i)
--   )
--   $ toSeqInner (iota n)

-- nestedIrregularSequenceRef :: Int -> Vector Int
-- nestedIrregularSequenceRef n = fromList (Z :. n) [P.sum [i + j | j <- [0..i-1]] | i <- [0..n-1]]
--
-- deepNestedSequence :: Int -> Acc (Vector Int)
-- deepNestedSequence n = asnd . collect
--   $ fromSeq
--   $ mapSeq
--   (\ i -> asnd . collect
--         $ fromSeq
--         $ mapSeq
--         (\ j -> collect
--               $ foldSeqE (+) 0
--               $ mapSeq
--               (\ k -> collect
--                     $ foldSeqE (+) 0
--                     $ toSeqInner (iota k)
--               )
--               $ toSeqInner (iota j)
--         )
--         $ toSeqInner (iota i)
--   )
--   $ toSeqInner (iota n)

-- deepNestedSequenceRef :: Int -> Vector Int
-- deepNestedSequenceRef n = fromList (Z :. P.length xs) xs
--   where xs = [P.sum [x | k <- [0..j-1], x <- [0..k-1]] | i <- [0..n-1], j <- [0..i-1]]

irregular :: Acc (Scalar Int) -> Acc (Scalar Int)
irregular n
  = collect
  $ foldSeqE (+) 0
  $ let s     = toSeqInner (iota n)
        f x y = A.zipWith (-) (A.sum x) (A.product y)
    in  zipWithSeq f
          (mapSeq iota s)
          (mapSeq (iota . A.map (the n -)) s)

enumeration :: Acc (Scalar Int) -> Acc (Scalar Int) -> Acc (Vector DIM1, Vector Int)
enumeration n x
  = collect
  . fromSeq
  $ produce (the n) (\i -> A.map (* the i) (iota x))

enumerationIncreasing :: Acc (Scalar Int) -> Acc (Vector DIM1, Vector Int)
enumerationIncreasing n
  = collect
  . fromSeq
  $ produce (the n) (\i -> iota i)

enumerationIrregular :: Acc (Vector Int) -> Acc (Vector DIM1, Vector Int)
enumerationIrregular ns
  = collect
  . fromSeq
  . mapSeq iota
  $ toSeqInner ns

regularFold :: (Shape sh, A.Num e) => Acc (Array (sh:.Int:.Int) e) -> Acc (Array (sh:.Int) e)
regularFold
  = collect
  . tabulate
  . mapSeq (fold (+) 0)
  . toSeqInner

irregularFold :: Acc (Scalar Int) -> Acc (Array DIM1 Int)
irregularFold n
  = collect
  . tabulate
  . mapSeq (fold (+) 0)
  $ produce (the n) iota

append :: Elt e => Acc (Array (Z :. Int :. Int) e) -> Acc (Array (Z :. Int :. Int) e) -> Acc (Vector e)
append xs ys
  = asnd
  $ collect
  $ fromSeq
  $ zipWithSeq (A.++)
      (toSeqOuter xs)
      (toSeqOuter ys)

appendIrregular :: Acc (Scalar Int) -> Acc (Scalar Int) -> Acc (Vector Int)
appendIrregular x y
  = asnd
  $ collect
  $ fromSeq
  $ zipWithSeq (A.++)
      (produce (the x) iota)
      (produce (the y) iota)

enumerationRef :: Int -> Int -> (Vector DIM1, Vector Int)
enumerationRef n x =
  let
    shs = P.replicate n (Z:.x)
    xs = [ P.map (*i) [0..x-1] | i <- [0..n-1]]
    res = concat xs
  in ( fromList (Z :. P.length shs) shs
     , fromList (Z :. P.length res) res)

enumerationIncreasingRef :: Int -> (Vector DIM1, Vector Int)
enumerationIncreasingRef n =
  let
      shs = [ Z:.i | i <- [0..n-1]]
      xs  = [ [0..i-1] | i <- [0..n-1]]
      res = concat xs
  in
  ( fromList (Z :. P.length shs) shs
  , fromList (Z :. P.length res) res
  )

enumerationIrregularRef :: Vector Int -> (Vector DIM1, Vector Int)
enumerationIrregularRef ns =
  let
      shs = [ Z:.i | i <- toList ns]
      xs  = [ [0..i-1] | i <- toList ns]
      res = concat xs
  in
  ( fromList (Z :. P.length shs) shs
  , fromList (Z :. P.length res) res
  )

appendRef :: Elt e => Array (Z :. Int :. Int) e -> Array (Z :. Int :. Int) e -> Vector e
appendRef as bs =
  let
      Z :. n :. m = Sugar.shape as
      Z :. r :. c = Sugar.shape bs
      xs          = [ [ as Sugar.! (Z :. i :. j) | j <- [0..m-1]] | i <- [0..n-1]]
      ys          = [ [ bs Sugar.! (Z :. i :. j) | j <- [0..c-1]] | i <- [0..r-1]]
      zs          = P.zipWith (P.++) xs ys
      res         = concat zs
  in
  fromList (Z :. P.length res) res

appendIrregularRef :: Int -> Int -> Vector Int
appendIrregularRef x y =
  let
      xs  = [ [0..i-1] | i <- [0..x-1]]
      ys  = [ [0..i-1] | i <- [0..y-1]]
      zs  = P.zipWith (P.++) xs ys
      res = concat zs
  in
  fromList (Z :. P.length res) res

irregularRef :: Int -> Scalar Int
irregularRef n = fromList Z [x]
  where
    x = P.sum [ P.sum [0..i-1] - P.product [0..n-i-1] | i <- [0..n-1] ]

regularFoldRef :: (Shape sh, P.Num e, Elt e) => Array (sh :. Int :. Int) e -> Array (sh :. Int) e
regularFoldRef a =
  let
      sh :. n :. m = Sugar.shape a
      xs           = [ [ P.sum [a Sugar.! (Sugar.fromIndex sh j :. k :. i) | k <- [0..n-1]] | j <- [0..Sugar.size sh - 1] ]
                       | i <- [0..m-1]
                     ]
  in
  fromList (sh:.m) (concat xs)

irregularFoldRef :: Int -> Array DIM1 Int
irregularFoldRef n
  = fromList (Z:.n)
  $ P.map P.sum
  $ P.map (P.enumFromTo 0 . (P.subtract 1)) [0..n-1]


subshapesOf :: Shape sh => sh -> Gen sh
subshapesOf sh = listToShape <$> mapM f (shapeToList sh)
  where
    f n = T.elements [i | i <- [1..n] , n `mod` i P.== 0]

subarrays1Ref :: Elt e => DIM1 -> Array DIM1 e -> Array DIM2 e
subarrays1Ref (Z:.n) xs
  = fromList (Z:.m:.n)
  . concat
  $ [ [xs Sugar.! (Z:.(y*n + x)) | x <- [0..n-1]] | y <- [0..m - 1]]
  where
    m = Sugar.size (Sugar.shape xs) `div` n

subarrays2Ref :: Elt e => DIM2 -> Array DIM2 e -> Array DIM3 e
subarrays2Ref (Z:.m:.n) xs
  = fromList (Z:.s:.m:.n)
  . concat
  $ [  [xs Sugar.! (Z:.(y' + m*y):.(x' + n*x)) | (y',x') <- (,) <$> [0..m-1] <*>  [0..n-1]]
       | (x,y) <- (,) <$> [0..n'-1] <*> [0..m'-1]
    ]
  where
    Z:.h:.w = arrayShape xs
    s       = Sugar.size (Sugar.shape xs) `div` (m * n)
    m'      = h `div` m
    n'      = w `div` n

