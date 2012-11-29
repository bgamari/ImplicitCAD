-- Implicit CAD. Copyright (C) 2011, Christopher Olah (chris@colah.ca)
-- Released under the GNU GPL, see LICENSE

{-# LANGUAGE TypeFamilies #-}

module Graphics.Implicit.Export.Render where

import Graphics.Implicit.Definitions
import Graphics.Implicit.Export.Render.Definitions
import Data.AffineSpace
import Data.AffineSpace.Point

-- Here's the plan for rendering a cube (the 2D case is trivial):

-- (1) We calculate midpoints using interpolate.
--	   This guarentees that our mesh will line up everywhere.
--	   (Contrast with calculating them in getSegs)

import Graphics.Implicit.Export.Render.Interpolate (interpolate)

-- (2) We calculate the segments separating the inside and outside of our
--	   object on the sides of the cube.
--	   getSegs internally uses refine from RefineSegs to subdivide the segs
--	   to better match the boundary.

import Graphics.Implicit.Export.Render.GetSegs (getSegs, getSegs')
-- import Graphics.Implicit.Export.Render.RefineSegs (refine)

-- (3) We put the segments from all sides of the cube together
--	   and extract closed loops.

import Graphics.Implicit.Export.Render.GetLoops (getLoops)

-- (4) We tesselate the loops, using a mixture of triangles and squares

import Graphics.Implicit.Export.Render.TesselateLoops (tesselateLoop)

-- (5) We try to merge squares, then turn everything into triangles.

import Graphics.Implicit.Export.Render.HandleSquares (mergedSquareTris)

-- Success: This is our mesh.

-- Each step is done in parallel using Control.Parallel.Strategies

import Control.Parallel.Strategies (using, rdeepseq, parListChunk)

-- The actual code is just a bunch of ugly argument passing.
-- Utility functions can be found at the end.

-- For efficiency, we need to avoid looking things up in other lists
-- (since they're 3D, it's an O(n³) operation...). So we need to make
-- our algorithms "flow" along the data structure instead of accessing
-- within it. To do this we use the ParallelListComp GHC extention.

-- We also compute lots of things in advance and pass them in as arguments,
-- to reduce redundant computations.

-- All in all, this is kind of ugly. But it is necessary.

-- Note: As far as the actual results of the rendering algorithm, nothing in
--		 this file really matters. All the actual decisions about how to build
--		 the mesh are abstracted into the imported files. They are likely what
--		 you are interested in.

import Data.Array.Repa (Array, Z(..), (:.)(..), DIM3, ix3, DIM2, ix2)
import qualified Data.Array.Repa as A
import qualified Data.Array.Repa.Repr.Vector as A
import qualified Data.Array.Repa.Unsafe as A
import Control.Monad.Identity (runIdentity)

import Data.VectorSpace

data R2 = R2 {-# UNPACK #-} !Float {-# UNPACK #-} !Float
		deriving (Show, Eq)

r2 (x,y)  = R2 x y
unR2 (R2 x y) = (x,y)

instance AdditiveGroup R2 where
    zeroV = R2 0 0
    R2 x y ^+^ R2 x' y' = R2 (x+x') (y+y')
    negateV (R2 x y) = R2 (-x) (-y)

instance VectorSpace R2 where
	type Scalar R2 = Float
	a *^ R2 x y = R2 (a*x) (a*y)

instance InnerSpace R2 where
	R2 x y <.> R2 x' y' = x*x' + y*y'

type P2 = Point R2

p2ToE2 = P . unR2 . unPoint
e2ToP2 = P . r2 . unPoint

data R3 = R3 {-# UNPACK #-} !Float
			 {-# UNPACK #-} !Float
			 {-# UNPACK #-} !Float
		deriving (Show, Eq)

r3 (x,y,z) = R3 x y z
unR3 (R3 x y z) = (x,y,z)

instance AdditiveGroup R3 where
    zeroV = R3 0 0 0
    R3 x y z ^+^ R3 x' y' z' = R3 (x+x') (y+y') (z+z')
    negateV (R3 x y z) = R3 (-x) (-y) (-z)

instance VectorSpace R3 where
	type Scalar R3 = Float
	a *^ R3 x y z = R3 (a*x) (a*y) (a*z)

instance InnerSpace R3 where
	R3 x y z <.> R3 x' y' z' = x*x' + y*y' + z*z'

type P3 = Point R3

p3ToE3 = P . unR3 . unPoint
e3ToP3 = P . r3 . unPoint

getMesh :: 𝔼3 -> 𝔼3 -> ℝ -> Obj3 -> TriangleMesh
getMesh p1 p2 res obj =
	let
		(dx,dy,dz) = p2 .-. p1
		P (x1,y1,z1) = p1
		P (x2,y2,z2) = p2

		-- How many steps will we take on each axis?
		nx = ceiling $ dx / res
		ny = ceiling $ dy / res
		nz = ceiling $ dz / res

		rx = dx/fromIntegral nx
		ry = dy/fromIntegral ny
		rz = dz/fromIntegral nz

		-- (0) Evaluate obj to avoid repeated computation
		indexToPos :: DIM3 -> P3
		indexToPos (Z:.x:.y:.z) = P (r3 (x1,y1,z1))
								.+^ r3 ( rx*fromIntegral x
									   , ry*fromIntegral y
									   , rz*fromIntegral z)

		objV :: Array A.U DIM3 ℝ
		objV = runIdentity $ A.computeP
			   $ A.fromFunction (ix3 (nx+3) (ny+3) (nz+3)) (obj . p3ToE3 . indexToPos)

		-- (1) Calculate mid-points on X, Y, and Z axis in 3D space.

		mids :: DIM3 -> (P3 -> Float) -> (P3 -> Float -> P3) -> (DIM3 -> DIM3)
			 -> Array A.U DIM3 Float
		mids size posToCoord coordToPos neighbor =
			A.deepSeqArray objV
			$ runIdentity $ A.computeP
			$ A.unsafeTraverse objV (const size)
			$ \lookupObj p -> let
								  coord = posToCoord . indexToPos
								  n = neighbor p
							  in interpolate (coord p, lookupObj p)
											 (coord n, lookupObj n)
											 (obj . p3ToE3 . coordToPos (indexToPos p))
											 res

		midsX = mids (ix3 nx (ny+1) (nz+1))
					 (\(P (R3 x y z))->x)
					 (\(P (R3 x y z)) x'->P $ r3 (x',y,z))
					 (\(Z:.x:.y:.z)->ix3 (x+1) y z)

		midsY = mids (ix3 (nx+1) ny (nz+1))
					 (\(P (R3 x y z))->y)
					 (\(P (R3 x y z)) y'->P $ r3 (x,y',z))
					 (\(Z:.x:.y:.z)->ix3 x (y+1) z)

		midsZ = mids (ix3 (nx+1) (ny+1) nz)
					 (\(P (R3 x y z))->z)
					 (\(P (R3 x y z)) z'->P $ r3 (x,y,z'))
					 (\(Z:.x:.y:.z)->ix3 x y (z+1))

		-- (2) Calculate segments for each side

		segs :: DIM3
			 -> (P3 -> (P2, ℝ))
			 -> (ℝ -> P2 -> P3)
			 -> (DIM3 -> DIM3) -> A.Array A.U DIM3 Float
			 -> (DIM3 -> DIM3) -> A.Array A.U DIM3 Float
			 -> Array A.V DIM3 [[P3]]
		segs size project expand neighA midsA neighB midsB =
			A.deepSeqArrays [midsX, midsY, midsZ]
			$ runIdentity $ A.computeP
			$ A.unsafeTraverse3 objV midsA midsB (\_ _ _ -> size)
			$ \lookupObj lookupMidA lookupMidB p ->
				let
					(p0, c0) = project $ indexToPos p
					(p1, _)  = project $ indexToPos $ neighA $ neighB p
				in map (map $ expand c0 . e2ToP2)
				   $ getSegs (p2ToE2 p0) (p2ToE2 p1)
							 (obj . p3ToE3 . expand c0 . e2ToP2)
							 ( lookupObj p
							 , lookupObj $ neighA p
							 , lookupObj $ neighB p
							 , lookupObj $ neighA $ neighB p
							 )
							 ( lookupMidB $ p, lookupMidB $ neighA p
							 , lookupMidA $ p, lookupMidA $ neighB p
							 )

		neighX (Z:.x:.y:.z) = ix3 (x+1)	 y	   z
		neighY (Z:.x:.y:.z) = ix3  x	(y+1)  z
		neighZ (Z:.x:.y:.z) = ix3  x	 y	  (z+1)

		segsX = let
					project (P (R3 x y z)) = (P $ r2 (y,z), x)
					expand x (P (R2 y z)) = P $ r3 (x,y,z)
					size = ix3 (nx+1) ny nz
				in segs size project expand neighY midsY neighZ midsZ

		segsY = let
					project (P (R3 x y z)) = (P $ r2 (x,z), y)
					expand y (P (R2 x z)) = P $ r3 (x,y,z)
					size = ix3 nx (ny+1) nz
				in segs size project expand neighX midsX neighZ midsZ

		segsZ = let
					project (P (R3 x y z)) = (P $ r2 (x,y), z)
					expand z (P (R2 x y)) = P $ r3 (x,y,z)
					size = ix3 nx ny (nz+1)
				in segs size project expand neighX midsX neighY midsY

		-- (3) & (4) : get and tesselate loops
		sqTris :: Array A.V DIM3 [TriSquare]
		sqTris =
		   A.deepSeqArrays [segsX, segsY, segsZ]
		   $ runIdentity $ A.computeP
		   $ A.unsafeTraverse3 segsX segsY segsZ (\_ _ _ -> ix3 nx ny nz)
		   $ \lookupSegX lookupSegY lookupSegZ p@(Z:.x:.y:.z) ->
				   concatMap (tesselateLoop res obj)
				 $ getLoops $ concat
				 $ (map (map (map p3ToE3)))
				 $ [		lookupSegX $ ix3  x	   y	 z
				   , mapR $ lookupSegX $ ix3 (x+1) y	 z
				   , mapR $ lookupSegY $ ix3  x	   y	 z
				   ,		lookupSegY $ ix3  x	  (y+1)	 z
				   ,		lookupSegZ $ ix3  x	   y	 z
				   , mapR $ lookupSegZ $ ix3  x	   y	(z+1)
				   ]
	
	in mergedSquareTris $ concat $ A.toList sqTris -- (5) merge squares, etc

getContour :: 𝔼2 -> 𝔼2 -> ℝ -> Obj2 -> [Polyline]
getContour p1@(P (x1,y1)) p2@(P (x2,y2)) res obj = 
	let
		(dx,dy) = p2 .-. p1

		-- How many steps will we take on each axis?
		nx = ceiling $ dx / res
		ny = ceiling $ dy / res

		rx = dx/fromIntegral nx
		ry = dy/fromIntegral ny

		-- Evaluate obj to avoid waste in mids, segs, later.
		indexToPos :: DIM2 -> P2
		indexToPos (Z:.x:.y) = P (r2 (x1,y1))
							   .+^ r2 ( rx*fromIntegral x
									  , ry*fromIntegral y
									  )

		objV :: Array A.U DIM2 ℝ
		objV = runIdentity $ A.computeP
			   $ A.fromFunction (ix2 (nx+2) (ny+2)) (obj . p2ToE2 . indexToPos)

		-- (1) Calculate mid poinsts on X, Y, and Z axis in 3D space.

		mids :: (P2 -> Float) -> (P2 -> Float -> P2) -> (DIM2 -> DIM2)
			 -> Array A.U DIM2 Float
		mids posToCoord coordToPos neighbor =
			runIdentity $ A.computeP
			$ A.traverse objV (\_ -> ix2 nx ny)
			$ \lookupObj p -> let
								coord = posToCoord . indexToPos
								n = neighbor p
							  in interpolate (coord p, lookupObj p)
											 (coord n, lookupObj n)
											 (obj . p2ToE2 . coordToPos (indexToPos p))
											 res

		midsX = mids (\(P (R2 x y))->x)
					 (\(P (R2 x y)) x'->P $ r2 (x',y))
					 (\(Z:.x:.y)->ix2 (x+1) y)

		midsY = mids (\(P (R2 x y))->y)
					 (\(P (R2 x y)) y'->P $ r2 (x,y'))
					 (\(Z:.x:.y)->ix2 x (y+1))

		-- Calculate segments for each side

		segs :: Array A.V DIM2 [[𝔼2]]
		segs =
			runIdentity $ A.computeP 
			$ A.traverse3 objV midsX midsY (\_ _ _ -> ix2 nx ny)
			$ \lookupObj lookupMidX lookupMidY p0@(Z:.x:.y) ->
				  let p1 = ix2 (x+1) (y+1)
				  in getSegs (p2ToE2 $ indexToPos p0) (p2ToE2 $ indexToPos p1) obj
							 ( lookupObj $ ix2	x	  y
							 , lookupObj $ ix2 (x+1)  y
							 , lookupObj $ ix2	x	 (y+1)
							 , lookupObj $ ix2 (x+1) (y+1)
							 )
							 ( lookupMidY p0, lookupMidY p1
							 , lookupMidX p0, lookupMidX p1
							 )

	in concat $ A.toList segs -- (5) merge squares, etc

mapR = map reverse

