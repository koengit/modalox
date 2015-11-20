module Modalox
  ( RelationType(..)
  , Modality(..)
  
  , Form(..)
  , atom, box, dia, (.&.), (.|.), (.->.), nt
  
  , M
  , run, define
  
  , litify
  , Model
  , prove
  )
 where

--------------------------------------------------------------------------------

import Data.List( sort, group, intercalate )
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad( when )
import Data.IORef

import SAT

--------------------------------------------------------------------------------

data RelationType
  = Reflexive
  | Transitive
 deriving ( Eq, Ord )

data Modality m
  = m :@ [RelationType]
  | Modality m :&&: Modality m
  | Modality m :||: Modality m
  | Star (Modality m)
 deriving ( Eq, Ord )

instance Show m => Show (Modality m) where
  show (m :@ rs)    = show m ++ (if Reflexive  `notElem` rs then "/" else "")
                             ++ (if Transitive `notElem` rs then "^" else "")
  show (m1 :&&: m2) = showM0 m1 ++ "&" ++ showM0 m2
  show (m1 :||: m2) = showM0 m1 ++ "|" ++ showM0 m2
  show (Star m)     = showM0 m ++ "*"

showM0 p@(_ :&&: _) = "(" ++ show p ++ ")"
showM0 p@(_ :||: _) = "(" ++ show p ++ ")"
showM0 p            = show p

--------------------------------------------------------------------------------

data Form m a
  = Box (Modality m) (Form m a)
  | Not (Form m a)
  | Form m a :&: Form m a
  | Atom a
 deriving ( Eq, Ord )

instance (Show m, Show a) => Show (Form m a) where
  show (Box m p) = "[" ++ show m ++ "]" ++ showF0 p
  show (Not p)   = "~" ++ showF0 p
  show (p :&: q) = showF0 p ++ " & " ++ showF0 q
  show (Atom x)  = show x

showF0 p@(_ :&: _) = "(" ++ show p ++ ")"
showF0 p           = show p

atom :: a -> Form m a
atom x = Atom x

box, dia :: Modality m -> Form m a -> Form m a
box m p = Box m p
dia m p = nt (box m (nt p))

(.&.), (.|.), (.->.) :: Eq m => Form m a -> Form m a -> Form m a
Box m p .&. Box m' q | m == m' = Box m (p .&. q)
p       .&. q                  = p :&: q

p .|.  q = nt (nt p .&. nt q)
p .->. q = nt p .|. q

nt :: Form m a -> Form m a
nt (Not p) = p
nt p       = Not p

--------------------------------------------------------------------------------

newtype M m a =
  M (Solver -> (String->IO()) ->
       IORef (M.Map (Form m Lit) (Bool, Bool, Lit)) ->
         IO ( a
            , [(Lit, Modality m, Lit)] -- boxs
            , [(Lit, Modality m, Lit)] -- dias
            ))

instance Functor (M m) where
  f `fmap` M m =
    M (\s say ref -> (\(x,boxs,dias) -> (f x, boxs, dias)) `fmap` m s say ref)

instance Monad (M m) where
  return x =
    M (\s say ref ->
      return (x, [], [])
    )
  
  M m1 >>= k =
    M (\s say ref ->
      do (x, boxs1, dias1) <- m1 s say ref
         let M m2 = k x
         (y, boxs2, dias2) <- m2 s say ref
         return (y, boxs1++boxs2, dias1++dias2)
    )

run :: Solver ->
       (String->IO()) ->
       M m a -> IO ( a
                   , [(Lit, Modality m, Lit)]
                   , [(Lit, Modality m, Lit)]
                   )
run s say (M m) =
  do ref <- newIORef M.empty
     m s say ref

--------------------------------------------------------------------------------

newAtom :: M m Lit
newAtom = M (\s say ref -> do x <- newLit s; return (x,[],[]))

addCls :: [Lit] -> M m ()
addCls xs = M (\s say ref -> do say (intercalate " | " (map show xs)); addClause s xs; return ((),[],[]))

addBoxPrim :: Lit -> Modality m -> Lit -> M m ()
addBoxPrim a m b = M (\s say ref -> return ((),[(a,m,b)],[]))

addDiaPrim :: Lit -> Modality m -> Lit -> M m ()
addDiaPrim a m b = M (\s say ref -> return ((),[],[(a,m,b)]))

look :: Ord m => Form m Lit -> M m (Maybe (Bool,Bool,Lit))
look p = M (\s say ref -> do mp <- readIORef ref; return (M.lookup p mp,[],[]))

store :: Ord m => Form m Lit -> (Bool,Bool,Lit) -> M m ()
store p t = M (\s say ref -> do mp <- modifyIORef ref (M.insert p t); return ((),[],[]))

say :: String -> M m ()
say t = M (\s say ref -> do say t; return ((),[],[]))

--------------------------------------------------------------------------------

addBox :: Lit -> Modality m -> Lit -> M m ()
addBox a (m1 :&&: m2) b =
  do addBox a m1 b
     addBox a m2 b

addBox a (m1 :||: m2) b =
  do a1 <- newAtom
     a2 <- newAtom
     addCls [neg a, a1, a2]
     addBox a1 m1 b
     addBox a2 m2 b

addBox a (Star m) b =
  do r <- newAtom
     addCls [neg a, r]
     addCls [neg r, b]
     addBox r m r

addBox a m@(lab:@rels) b
  | Reflexive `elem` rels && Transitive `elem` rels =
    do r <- newAtom
       addCls [neg a, r]
       addCls [neg r, b]
       addBoxPrim r m r
  
  | Transitive `elem` rels =
    do r1 <- newAtom
       r2 <- newAtom
       addCls [neg a, r1]
       addCls [neg r2, b]
       addCls [neg r2, r1]
       addBoxPrim r1 m r2
  
  | otherwise =
    do when (Reflexive `elem` rels) $
         addCls [neg a, b]
       addBoxPrim a m b

--------------------------------------------------------------------------------

addDia :: Show m => Lit -> Modality m -> Lit -> M m ()
addDia a (m1 :||: m2) b =
  do addDia a m1 b
     addDia a m2 b

addDia a (m1 :&&: m2) b =
  do a1 <- newAtom
     a2 <- newAtom
     addCls [neg a, a1, a2]
     addDia a1 m1 b
     addDia a2 m2 b

addDia a (Star m) b =
  error ("using the modality <" ++ show (Star m) ++ "> -- sorry!")

addDia a m@(lab:@rels) b =
  do addDiaPrim a m b

--------------------------------------------------------------------------------

atomFor :: (Show m, Ord m) => Bool -> Bool -> Form m Lit -> (Lit -> M m ()) -> (Lit -> M m ()) -> M m Lit
atomFor impls impld p mkImpls mkImpld =
  do mbbx <- look p
     entry@(_,_,x) <-
       case mbbx of
         Just (impls', impld', x) ->
           do when (impls && not impls') (mkImpls x)
              when (impld && not impld') (mkImpld x)
              return (impls || impls', impld || impld', x)
         
         Nothing ->
           do x <- (if impld then neg else id) `fmap` newAtom
              --say (show x ++ " = " ++ show p)
              when impls (mkImpls x)
              when impld (mkImpld x)
              return (impls, impld, x)
     store p entry
     return x

--------------------------------------------------------------------------------

define :: (Show m, Ord m) => Bool -> Bool -> Form m Lit -> M m Lit
define impls impld (Box m p) =
  do a <- define impls impld p
     atomFor impls impld (Box m (Atom a))
       (\x -> addBox x m a)
       (\x -> addDia (neg x) m (neg a))

define impls impld (Not p) =
  -- switching impls<->impld
  neg `fmap` define impld impls p

define impls impld (p :&: q) =
  do a <- define impls impld p
     b <- define impls impld q
     atomFor impls impld (if a <= b then Atom a :&: Atom b
                                    else Atom b :&: Atom a)
       (\x -> do addCls [neg x, a]
                 addCls [neg x, b])
       (\x -> do addCls [neg a, neg b, x])

define impls impld (Atom a) =
  do return a

--------------------------------------------------------------------------------

litify :: Ord a => Solver -> Form m a -> M.Map a Lit -> IO (Form m Lit, M.Map a Lit)
litify s (Box m p) mp =
  do (p',mp') <- litify s p mp
     return (Box m p',mp')

litify s (p :&: q) mp =
  do (p',mp1) <- litify s p mp
     (q',mp2) <- litify s q mp1
     return (p' :&: q',mp2)

litify s (Not p) mp =
  do (p',mp') <- litify s p mp
     return (Not p',mp')

litify s (Atom a) mp =
  case M.lookup a mp of
    Just x ->
      return (Atom x,mp)
    
    Nothing ->
      do x <- newLit s
         return (Atom x, M.insert a x mp)

--------------------------------------------------------------------------------

type Model = S.Set Lit

prove :: Eq m => Solver -> (String->IO()) -> [Model] -> [(Lit,m,Lit)] -> [(Lit,m,Lit)] -> [Lit]
      -> IO (Either [Model] [Lit])
prove s say seen boxs dias ass
  | any (S.fromList ass `S.isSubsetOf`) seen =
    do return (Left seen)

  | otherwise =
    do b <- solve s ass
       if b then
         do mod <- getModel s (ass ++ [ b | (_,_,b) <- boxs ] ++ [ b | (_,_,b) <- dias ])
            mseen <- check s say (mod:seen) boxs dias ass
            case mseen of
              Nothing    -> prove s say [] boxs dias ass
              Just seen' -> return (Left seen')
        else
         do cs <- conflict s
            return (Right [ a | a <- ass, neg a `elem` cs ])
 where
  getModel s xs =
    do bs <- sequence [ modelValue s x | x <- xs ]
       return (S.fromList [ if b then x else neg x | (b,x) <- bs `zip` xs ])

check :: Eq m => Solver -> (String->IO()) -> [Model] -> [(Lit,m,Lit)] -> [(Lit,m,Lit)] -> [Lit]
      -> IO (Maybe [Model])
check s say seen boxs dias ass =
  do -- fetch triggered boxs
     vs <- sequence [ modelValue s a | (a,_,_) <- boxs ]
     let boxs' = [ amb | (True,amb) <- vs `zip` boxs ]
     
     -- fetch triggered dias
     ws <- sequence [ modelValue s a | (a,_,_) <- dias ]
     let dias' = [ amb | (True,amb) <- ws `zip` dias ]
     
     -- check all triggered dias
     let chk seen [] =
           do return (Just seen)
         
         chk seen ((a,m,b):dias') =
           do res <- prove s say seen boxs dias (b:ass')
              case res of
                Left seen' ->
                  do chk seen' dias'
                  
                Right sub ->
                  do putStrLn (map show ass' `implies` show (neg a))
                     addClause s (neg a : map neg ass'')
                     return Nothing
                 where
                  ass'' = [ a
                          | b <- sub
                          , a <- take 1 [ a | (a,m',b') <- boxs', m' == m, b' == b ]
                          ]
           where
            ass' = usort [ b | (a,m',b) <- boxs', m' == m ]

         [] `implies` b = b
         as `implies` b = intercalate " & " as ++ " -> " ++ b

      in chk seen dias'
  
---

usort xs = map head . group . sort $ xs

