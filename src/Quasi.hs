{-# LANGUAGE
      FlexibleInstances,
      RelaxedPolyRec,
      RankNTypes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances #-}
module Quasi (
  pa, ty, ex
) where

import Loc ((<<@))
import Syntax
import Parser
import Util

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

pa, ty, ex :: QuasiQuoter
pa = mkQuasi (\_ _ -> parsePatt)

ty = QuasiQuoter qexp qpat where
  qexp s = do
    (stx, _) <- qeither s
    either toExpQ toExpQ stx
  qpat s = do
    (stx, _) <- qeither s
    either toPatQ toPatQ stx
  qeither s =
    parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (parseType :: P TypeT)     >>! Left
               else (parseType :: P (Type ())) >>! Right
      return (stx, lflag)

ex = QuasiQuoter qexp qpat where
  qexp s = do
    (stx, lflag) <- qeither s
    ast <- either toExpQ toExpQ stx
    case lflag of
      Just loc -> [| $(return ast) <<@ $(mkvarE loc) |]
      Nothing  -> return ast
  qpat s = do
    (stx, lflag) <- qeither s
    ast <- either toPatQ toPatQ stx
    case (lflag, ast) of
      (Just loc, TH.RecP n fs)
             -> TH.recP n (TH.fieldPat (TH.mkName "eloc_")
                                       (mkvarP loc) : map return fs)
      (_, _) -> return ast
  qeither s =
    parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (parseExpr :: P ExprT)     >>! Left
               else (parseExpr :: P (Expr ())) >>! Right
      return (stx, lflag)

mkQuasi       :: Data a => (Bool -> Maybe String -> P a) -> QuasiQuoter
mkQuasi parser = QuasiQuoter qexp qpat where
  qexp s = parseQuasi s parser >>= toExpQ
  qpat s = parseQuasi s parser >>= toPatQ

{-
mk :: forall f. (Data (f ()), Data (f TyTag),
                 Relocatable (f ()), Relocatable (f TyTag)) =>
      (forall i. Data i => P (f i)) -> QuasiQuoter
mk p = QuasiQuoter qexp qpat where
  qexp s = do
    (stx, lflag) <- parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (p :: P (f TyTag)) >>! Left
               else (p :: P (f ()))    >>! Right
      return (stx, lflag)
    ast <- either toExpQ toExpQ stx
    case lflag of
      Just loc -> [| $(return ast) <<@ $(mkvarE loc) |]
      Nothing  -> return ast
  qpat s = do
    (stx, lflag) <- parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (p :: P (f TyTag))     >>! Left
               else (p :: P (f ())) >>! Right
      return (stx, lflag)
    ast <- either toPatQ toPatQ stx
    case (lflag, ast) of
      (Just loc, TH.RecP n fs)
             -> TH.recP n (TH.fieldPat (TH.mkName "eloc_")
                                       (mkvarP loc) : map return fs)
      (_, _) -> return ast
-}

toExpQ :: Data a => a -> TH.ExpQ
toExpQ  = dataToExpQ antiExp

toPatQ :: Data a => a -> TH.PatQ
toPatQ  = dataToPatQ antiPat

antiExp :: Data a => a -> Maybe TH.ExpQ
antiExp  = const Nothing
           `extQ` antiPaExp
           `extQ` antiTyExp
           `extQ` antiTtExp
           `extQ` antiTiExp
           `extQ` (antiExExp :: Expr () -> Maybe TH.ExpQ)
           `extQ` (antiExExp :: ExprT -> Maybe TH.ExpQ)

antiPat :: Data a => a -> Maybe TH.PatQ
antiPat  = const Nothing
           `extQ` antiPaPat
           `extQ` (antiTyPat :: Type () -> Maybe TH.PatQ)
           `extQ` (antiTyPat :: TypeT -> Maybe TH.PatQ)
           `extQ` antiTiPat
           `extQ` (antiExPat :: Expr () -> Maybe TH.PatQ)
           `extQ` (antiExPat :: ExprT -> Maybe TH.PatQ)

antiPaExp :: Patt -> Maybe TH.ExpQ
antiPaExp (PaAnti anti) = Just $ case anti of
  Anti "lid"     v -> [| PaVar $(mkvarE v) |]
  Anti "name"    v -> [| PaVar (Lid $(mkvarE v)) |]
  Anti "str"     v -> [| PaLit (LtStr $(mkvarE v)) |]
  Anti "int"     v -> [| PaLit (LtInt $(mkvarE v)) |]
  Anti "float"   v -> [| PaLit (LtFloat $(mkvarE v)) |]
  Anti "anti"    v -> [| PaAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiPaExp _             = Nothing

antiPaPat :: Patt -> Maybe TH.PatQ
antiPaPat (PaAnti anti) = Just $ case anti of
  Anti "lid"     v -> con1P "PaVar" v
  Anti "name"    v -> con1P "PaVar" (con1P "Lid" v)
  Anti "str"     v -> con1P "PaLit" (con1P "LtStr" v)
  Anti "int"     v -> con1P "PaLit" (con1P "LtInt" v)
  Anti "float"   v -> con1P "PaLit" (con1P "LtFloat" v)
  Anti "anti"    v -> con1P "PaAnti" v
  Anti ""        v -> toPat v
  Anti t         _ -> unrec t
antiPaPat _             = Nothing

antiTyExp :: Type () -> Maybe TH.ExpQ
antiTyExp (TyAnti anti) = Just $ case anti of
  Anti "lid"     v -> [| TyCon $(mkvarE v) [] () |]
  Anti "name"    v -> [| TyCon (qlid $(mkvarE v)) [] () |]
  Anti "tv"      v -> [| TyVar $(mkvarE v) |]
  Anti "anti"    v -> [| TyAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiTyExp (TyCon n [TyAnti (Anti "list" v)] i)
  = Just [| TyCon $(toExpQ n) $(mkvarE v) $(toExpQ i) |]
antiTyExp _             = Nothing

antiTtExp :: TypeT -> Maybe TH.ExpQ
antiTtExp (TyAnti anti) = Just $ case anti of
  Anti "tv"      v -> [| TyVar $(mkvarE v) |]
  Anti "anti"    v -> [| TyAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiTtExp (TyCon n [TyAnti (Anti "list" v)] i)
  = Just [| TyCon $(toExpQ n) $(mkvarE v) $(toExpQ i) |]
antiTtExp _             = Nothing

antiTyPat :: Data i => Type i -> Maybe TH.PatQ
antiTyPat (TyAnti anti) = Just $ case anti of
  Anti "qlid"    v -> mkconP "TyCon" [toPat v, TH.listP [], TH.wildP]
  Anti "lid"     v -> mkconP "TyCon" [con2P "J" (TH.listP []) v,
                                      TH.listP [], TH.wildP]
  Anti "name"    v -> mkconP "TyCon" [con2P "J" (TH.listP [])
                                                (con1P "Lid" (toPat v)),
                                      TH.listP [], TH.wildP]
  Anti "tv"      v -> con1P "TyVar" v
  Anti "anti"    v -> con1P "TyAnti" v
  Anti ""        v -> toPat v
  Anti t         _ -> unrec t
antiTyPat (TyCon n [TyAnti (Anti "list" v)] i)
  = Just $ mkconP "TyCon" [ toPatQ n, mkvarP v, toPatQ i ]
antiTyPat _             = Nothing

antiTiExp :: TyTag -> Maybe TH.ExpQ
antiTiExp (TyTagAnti anti) = Just $ case anti of
  Anti "td"      v -> case getTdByName v of
                        Nothing -> fail $
                          "Unrecognized type name: " ++ v
                        Just td -> dataToExpQ (const Nothing) td
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiTiExp _             = Nothing

antiTiPat :: TyTag -> Maybe TH.PatQ
antiTiPat (TyTagAnti anti) = Just $ case anti of
  Anti "td"      v -> case getTdByName v of
                        Nothing -> fail $
                          "Unrecognized type name: " ++ v
                        Just td -> dataToPatQ (const Nothing) td
  Anti ""        v -> mkvarP v
  Anti t         _ -> unrec t
antiTiPat _             = Nothing

antiExExp :: Data i => Expr i -> Maybe TH.ExpQ
antiExExp = Just . loop where
  loop e0 = case view e0 of
    ExId i        -> [| exId $(toExpQ i) |]
    ExLit lt      -> [| exLit $(toExpQ lt) |]
    ExCase e bs   ->
      [| exCase $(loop e)
                $(TH.listE [ [| ($(toExpQ pj), $(loop ej)) |]
                           | (pj, ej) <- bs ]) |]
    ExLetRec bs e -> [| exLetRec $(toExpQ bs)$ $(loop e) |]
    ExLetDecl d e -> [| exLetDecl $(toExpQ d) $(loop e) |]
    ExPair e1 e2  -> [| exPair $(loop e1) $(loop e2) |]
    ExAbs x t e   -> [| exAbs $(toExpQ x) $(toExpQ t) $(loop e) |]
    ExApp e1 e2   -> [| exApp $(loop e1) $(loop e2) |]
    ExTAbs tv e   -> [| exTAbs $(toExpQ tv) $(loop e) |]
    ExTApp e t    -> [| exTApp $(loop e) $(toExpQ t) |]
    ExPack mt t e -> [| exPack $(toExpQ mt) $(toExpQ t) $(loop e) |]
    ExCast e mt t -> [| exCast $(loop e) $(toExpQ mt) $(toExpQ t) |]
    ExAnti a      -> case a of
      Anti "name"    v -> [| exBVar (Lid $(mkvarE v)) |]
      Anti "uname"   v -> [| exBCon (Uid $(mkvarE v)) |]
      Anti "qname"   v -> [| exVar (qlid $(mkvarE v)) |]
      Anti "quname"  v -> [| exCon (quid $(mkvarE v)) |]
      Anti "lid"     v -> [| exBVar $(mkvarE v) |]
      Anti "uid"     v -> [| exBCon $(mkvarE v) |]
      Anti "qlid"    v -> [| exVar $(mkvarE v) |]
      Anti "quid"    v -> [| exCon $(mkvarE v) |]
      Anti "id"      v -> [| exId $(mkvarE v) |]
      Anti "int"     v -> [| exInt $(mkvarE v) |]
      Anti "str"     v -> [| exStr $(mkvarE v) |]
      Anti "float"   v -> [| exFloat $(mkvarE v) |]
      Anti ""        v -> mkvarE v
      Anti t         _ -> unrec t

antiExPat :: Data i => Expr i -> Maybe TH.PatQ
antiExPat e = Just $ case view e of
  ExAnti a -> case a of
    Anti "name"    v -> exprP (exIdP (jP nulP (varP (lidP v))))
    Anti "uname"   v -> exprP (exIdP (jP nulP (conP (uidP v))))
    Anti "qname"   v -> exprP (exIdP (jP ('q':v) (varP (lidP v))))
    Anti "quname"  v -> exprP (exIdP (jP ('q':v) (conP (uidP v))))
    Anti "lid"     v -> exprP (exIdP (jP nulP (varP v)))
    Anti "uid"     v -> exprP (exIdP (jP nulP (conP v)))
    Anti "qlid"    v -> exprP (exIdP (jP ('q':v) (varP v)))
    Anti "quid"    v -> exprP (exIdP (jP ('q':v) (conP v)))
    Anti "id"      v -> exprP (exIdP v)
    Anti "int"     v -> exprP (con1P "ExLit" (con1P "LtInt" v))
    Anti "str"     v -> exprP (con1P "ExLit" (con1P "LtStr" v))
    Anti "float"   v -> exprP (con1P "ExLit" (con1P "LtFloat" v))
    Anti ""        v -> mkvarP v
    Anti t         _ -> unrec t
  e' -> exprP (toPatQ e')
  where exIdP a = con1P "ExId" a
        jP p    = con2P "J" p
        nulP    = TH.listP []
        varP a  = con1P "Var" a
        lidP a  = con1P "Lid" a
        conP a  = con1P "Con" a
        uidP a  = con1P "Uid" a
        exprP  :: TH.PatQ -> TH.PatQ
        exprP p = TH.recP (TH.mkName "Expr")
                          [TH.fieldPat (TH.mkName "expr_") p]

---
--- Syntax helpers
---

mkvarE :: String -> TH.ExpQ
mkvarP :: String -> TH.PatQ

mkvarE  = TH.varE . TH.mkName
mkvarP  = TH.varP . TH.mkName

mkconP :: String -> [TH.Q TH.Pat] -> TH.Q TH.Pat
mkconP n args = TH.conP (TH.mkName n) args

class ToPat a where toPat :: a -> TH.PatQ
instance ToPat TH.PatQ where toPat = id
instance ToPat String  where toPat = mkvarP

con1P :: ToPat a => String -> a -> TH.PatQ
con1P n arg = mkconP n [toPat arg]

con2P :: (ToPat a, ToPat b) =>
         String -> a -> b -> TH.PatQ
con2P n arg1 arg2 = mkconP n [toPat arg1, toPat arg2]

unrec :: Monad m => String -> m a
unrec = fail . ("Unrecognized antiquote type: " ++)
