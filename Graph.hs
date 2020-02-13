{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module Graph where

import Control.Lens hiding (Empty)

import qualified Data.Array as A
import Data.Ix
import Data.IORef
import Debug.Trace
import Control.Monad
import Control.Monad.State

type DegreeTable = A.Array Int Int


data Link = Empty | Link {_lTarget :: Vertex, _lEdge :: Int}
    deriving Eq
data VertexData = VD { _vdPredecessor :: Link,
                       _vdSuccessor :: Link,
                       _vdLabel :: Int}
                       
type Vertex = IORef VertexData

data Stack = Stack { _stA2 :: [(Int,Int)],
                     _stB12 :: [Int],
                     _stB22 :: [Int]}

makeLenses ''Link
makeLenses ''VertexData
makeLenses ''Stack

instance Show Link where
    show Empty = " X "
    show (Link _ e) = "  - [" ++ show e ++ "] -" 
instance Show VertexData where
    show (VD pred next lbl) = show pred ++ " [Vertex " ++ show lbl ++ "] " ++ show next
-- Retourne les indices de tous les éléments ayant la valeur 1
findUnhappyVertices t = [i | i <- range $ A.bounds t, t A.! i == 1]




testTab = A.listArray (1,10) $ [10,2,5,1,1,2,1,5,1,2]
maxVal = 100000


{-| ATTENTION TODO : Le cas où on teste pour la PREMIERE et la DERNIERE case n'est pas géré -}
{-| Retourne l'indice du premier élément à gauche de i non nul -}
neighborhoodL t i = neighborhoodL' t (i-1)
    where neighborhoodL' t k 
            | t A.! k == 0 = neighborhoodL' t (k-1) 
            | otherwise = k
  
{-| Retourne l'indice du premier élément à droite de i non nul -}
neighborhoodR t i = neighborhoodR' t (i+1)
    where neighborhoodR' t k 
            | t A.! k == 0 = neighborhoodR' t (k+1) 
            | otherwise = k


createVertex :: Int -> IO Vertex
createVertex i = newIORef $ VD Empty Empty i

{- V' est predecesseur de v -}
setPredecessor v v' val = do
    modifyIORef' v $ vdPredecessor .~ Link v' val
    modifyIORef' v' $ vdSuccessor .~ Link v val

setSucessor v v' val = setPredecessor v' v val


{-| Génère l'arc reliant les voisins gauche et droit du sommet de l'indice i.
 - Attention : les cas limites ne sont pas gérés (les voisins gauche/droit doivent exister) -}
buildEdge :: DegreeTable -> Int -> IO (Vertex,Vertex)
buildEdge  t i = do
        (v,v') <- (,) <$> createVertex (i - neighL) <*> createVertex rightVal
        setSucessor v v' i
        pure (v,v')
        
    where neighL = neighborhoodL t i
          neighR = neighborhoodR t i
          rightVal
                | i == snd (A.bounds t) = i - neighL + 1
                | otherwise = neighR - i
        
{-| Construit le graphe final selon la règle de l'étape 1 -}
buildGraph :: DegreeTable -> IO [Vertex]
buildGraph t 
        | null ones = error "Aucun degré 1"
        | otherwise = buildGraph' ones []
    where ones = findUnhappyVertices t
          (fstIndex, astIndex) = A.bounds t
          buildGraph' [] vertices = pure vertices
          buildGraph' (i:is) vertices
                | i == fstIndex = undefined
                | otherwise = do
                    (v,v') <- buildEdge t i
                    if t A.! neighborhoodL t i == 1
                        then do setSucessor (last vertices) v' i
                                buildGraph' is $ vertices ++ [v']
                        else buildGraph' is (vertices ++ [v,v'])

{- Vertex cover d'un segment -}
               
vertexCoverWith :: Vertex -> IO (Int,[Vertex])
vertexCoverWith v = do
    val <- readIORef v
    case _vdSuccessor val of 
        Empty -> pure (_vdLabel val, [v])
        Link nxt _ -> do
            (recVal, recVC) <- vertexCover nxt
            pure $ (_vdLabel val + recVal, v:recVC)
    
vertexCover :: Vertex -> IO (Int, [Vertex])
vertexCover v = do
    val <- readIORef v
    case _vdSuccessor val of
        Empty -> pure (0, [])
        Link nxt _ -> do
            (with,withVC) <- vertexCoverWith nxt -- NO
            (without,withoutVC) <- vertexCover nxt --YES
            if with < without+ _vdLabel val
                then pure (with,withVC)
                else pure (without + _vdLabel val, v:withoutVC)

{- Vertex cover sur une liste de segments -}
vertexCoverGraph vertices = do
        cc <- connexComponents
        forM cc vertexCover

    where connexComponents = do
            vals <- forM vertices readIORef
            pure [vi | (vi,val) <- zip vertices vals, _vdPredecessor val == Empty]
    
-- retourne (jocker, dette, nb fleches)
debtCount :: DegreeTable -> [Vertex] -> StateT Stack IO (Int,Int,Int)
debtCount t [] = pure (0,0,0)
debtCount t (v:vs) = do
        vdata <- liftIO $ readIORef v
        ((j,val,sol), list) <- debCount' vdata
        (jfinal, valfinal,solFinal) <- debtCount t list 
        pure (jfinal + j, val + valfinal,sol+solFinal)
    where debCount' vdata@(VD pred nxt lbl) 
                -- Cas B1
                | pred == Empty = 
                                  let nxtEdgeVal = _lEdge nxt
                                      val = t A.! (neighborhoodL t nxtEdgeVal)
                                  in if val >= 3
                                        then pure ((lbl,0,lbl),vs)
                                        else do
                                            stB12 %= (++[abs lbl])
                                            pure ((0, -lbl, lbl),vs)
                -- Cas B2
                | nxt == Empty = 
                                 let predEdgeVal = _lEdge pred
                                     val = t A.! (neighborhoodR t predEdgeVal)
                                 in if val >= 3
                                        then pure ((lbl,0,lbl),vs)
                                        else do 
                                          stB22 %= (++[abs lbl])
                                          pure ((0, lbl,lbl),vs)
                -- Cas A1
                | null vs || _lTarget nxt /= (head vs) = trace ("cas A1") $ pure ((lbl,0,lbl),vs)

                -- Cas A2
                | otherwise = trace ("cas A2") $ do
                     nxtData <- liftIO $ readIORef (_lTarget nxt)
                     let val = lbl - _vdLabel nxtData
                     stA2 %= (++[(abs lbl, abs $ _vdLabel nxtData)])
                     pure ((0, val, lbl + _vdLabel nxtData) ,tail vs)

stackAnalyser :: Stack -> (Int,Int,Int) -> (Int,Int,Int)
stackAnalyser (Stack a2 b12 b22) (j,val,nbfleches) 
    | j > abs val =  (((j-abs val) `mod` 2),0,j+abs val)
    | debt >= -1 = (0,finalDebtA,finalSolA)
    | debt <= -5 = (0, finalDebtB, finalSolB)
    | otherwise = (0,debt,j + abs val)
  where debt 
            | val >= 0 = val - j
            | otherwise = val + j
        (finalDebtA, finalSolA) = computeSolRecA debt nbfleches b22 a2
        (finalDebtB, finalSolB) = computeSolRecB debt nbfleches b12 a2
        computeSolRecA partDebt sol [] ((x,y):a2s) 
            | partDebt == 0 = (partDebt, sol)
            | partDebt < -1 = (partDebt,sol)
            | x * 3 <= abs partDebt = computeSolRecA (partDebt - x*3) (sol + x) [] a2s
            | otherwise = (partDebt - ceiling (fromIntegral partDebt / 3) * 3,
                           sol + ceiling (fromIntegral partDebt / 3))
        computeSolRecA partDebt sol (x:b22s) a2s
            | partDebt == 0 = (partDebt, sol)
            | partDebt < -1 = (partDebt,sol)
            | x * 3 < abs partDebt = computeSolRecA (partDebt - x*3) (sol + x) b22s a2s
            | otherwise = (partDebt - ceiling (fromIntegral partDebt / 3) * 3,
                            sol + ceiling (fromIntegral partDebt / 3))
        computeSolRecB partDebt sol [] ((x,y):a2s) 
            | partDebt == 0 = (partDebt, sol)
            | partDebt > -5 = (partDebt, sol)
            | y * 3 <= abs partDebt = computeSolRecB (partDebt + y*3) (sol + y) [] a2s
            | otherwise = (partDebt + ceiling (fromIntegral partDebt / 3) * 3,
                           sol + ceiling (fromIntegral partDebt / 3))
        computeSolRecB partDebt sol (x:b12s) a2s
            | partDebt == 0 = (partDebt, sol)
            | partDebt > -5 = (partDebt,sol) 
            | x * 3 <= abs partDebt = computeSolRecB (partDebt + x) (sol + x) b12s a2s
            | otherwise = (partDebt + ceiling (fromIntegral partDebt / 3) * 3,
                           sol + ceiling (fromIntegral partDebt / 3))
                
{- Debug part -}

testTab2 :: DegreeTable
testTab2 = A.listArray (1,16) [40,8,0,1,1,1,8,0,0,1,0,0,2,1,0,8]

testTab3 :: DegreeTable
testTab3 = A.listArray (1,length l) l
    where l = [8,1,0,1,1,1,8,7,0,0,1,8,1,1,0,1,7,2,1,0,1,2,40]
testTab4 :: DegreeTable
testTab4 = A.listArray (1,length l) l
    where l = [8,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,8]

mkDegreeTable :: [Int] -> DegreeTable
mkDegreeTable l = A.listArray (1,length l) l
testTab5 = mkDegreeTable [8,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,8]
testTab6 = mkDegreeTable [8,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,8]
testTab7 = mkDegreeTable ([8,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,0,0,0,8])
testTab8 = mkDegreeTable [8,0,1,1,0,1,0,7,0,1,0,0,1,1,1,9,1,0,0,1,0,0,0,7,0,1,8,0,1,8] -- to test
testTab9 = mkDegreeTable [8,1,1,1,9,1,0,0,1,8]





dumpVertex v = do
    x <- readIORef v
    pure $ show  x

dumpVertexList l = do
    x <- forM l dumpVertex
    putStrLn $ unlines x

test t = do
    g <- buildGraph t
    vcret <- vertexCoverGraph g
    dumpVertexList $ concat (snd <$> vcret)
    (ret, stacks) <- runStateT (debtCount t $ concat (snd <$> vcret)) mkStack
    print ret
    print $ stackAnalyser stacks ret
    
mkStack = Stack [] [] []
