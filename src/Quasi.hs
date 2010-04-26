{-# LANGUAGE
      FlexibleInstances,
      RelaxedPolyRec,
      RankNTypes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances #-}
module Quasi (
  pa, ty, ex, dc
) where

import Loc as Loc
import Syntax
import Parser
import Util

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

pa, ty, ex, dc :: QuasiQuoter

pa = QuasiQuoter qexp qpat where
  qexp s = parseQuasi s (\_ _ -> parsePatt) >>= toExpQ
  qpat s = parseQuasi s (\_ _ -> parsePatt) >>= toPatQ

ex = mkQuasi parseExpr $ \ast loc -> [| $(ast) <<@ $(mkvarE loc) |]
dc = mkQuasi parseDecl $ \ast loc -> [| $(ast) <<@ $(mkvarE loc) |]
ty = mkQuasi parseType const

mkQuasi :: forall f. (Data (f ()), Data (f TyTag)) =>
      (forall i. TyTagMode i => P (f i)) ->
      (TH.ExpQ -> String -> TH.ExpQ) ->
      QuasiQuoter
mkQuasi parser reloc = QuasiQuoter qexp qpat where
  qexp s = do
    (stx, lflag) <- parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (parser :: P (f TyTag)) >>! Left
               else (parser :: P (f ()))    >>! Right
      return (stx, lflag)
    ast <- either toExpQ toExpQ stx
    case lflag of
      Just loc -> reloc (return ast) loc
      Nothing  -> return ast
  qpat s = do
    (stx, lflag) <- parseQuasi s $ \iflag lflag -> do
      stx <- if iflag
               then (parser :: P (f TyTag))     >>! Left
               else (parser :: P (f ())) >>! Right
      return (stx, lflag)
    ast <- either toPatQ toPatQ stx
    case (lflag, ast) of
      (Just loc, TH.RecP n fs)
             -> TH.recP n (TH.fieldPat (TH.mkName "eloc_")
                                       (mkvarP loc) : map return fs)
      (Just loc, TH.ConP n (TH.WildP:ps))
             -> TH.conP n (mkvarP loc : map return ps)
      (_, _) -> return ast

toExpQ :: Data a => a -> TH.ExpQ
toExpQ  = dataToExpQ antiExp

toPatQ :: Data a => a -> TH.PatQ
toPatQ  = dataToPatQ antiPat

antiExp :: Data a => a -> Maybe TH.ExpQ
antiExp  = const Nothing
           `extQ` antiQuExp
           `extQ` antiTvExp
           `extQ` antiUidExp
           `extQ` antiLidExp
           `extQ` antiQLidExp
           `extQ` antiQUidExp
           `extQ` antiPaExp
           `extQ` antiTiExp
           `extQ` antiTuExp `extQ` antiTtExp
           `ext1Q` antiExExp
           `ext1Q` antiDcExp
           `ext1Q` antiMeExp

antiPat :: Data a => a -> Maybe TH.PatQ
antiPat  = const Nothing
           `extQ` antiLocPat
           `extQ` antiUnitPat
           `extQ` antiQuPat
           `extQ` antiTvPat
           `extQ` antiUidPat
           `extQ` antiLidPat
           `extQ` antiQLidPat
           `extQ` antiQUidPat
           `extQ` antiPaPat
           `extQ` antiTiPat
           `ext1Q` antiTyPat
           `ext1Q` antiExPat
           `ext1Q` antiDcPat
           `ext1Q` antiMePat

antiLocPat :: Loc.Loc -> Maybe TH.PatQ
antiLocPat _ = Just TH.wildP

antiUnitPat :: () -> Maybe TH.PatQ
antiUnitPat _ = Just TH.wildP

antiMeExp :: Data i => ModExp i -> Maybe TH.ExpQ
antiMeExp (MeAnti anti) = Just $ case anti of
  Anti "uname"   v -> [| MeName (J [] (Uid $(mkvarE v))) |]
  Anti "quname"  v -> [| MeName (quid $(mkvarE v)) |]
  Anti "uid"     v -> [| MeName (J [] $(mkvarE v)) |]
  Anti "quid"    v -> [| MeName $(mkvarE v) |]
  Anti "anti"    v -> [| MeAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiMeExp _             = Nothing

antiMePat :: Data i => ModExp i -> Maybe TH.PatQ
antiMePat (MeAnti anti) = Just $ case anti of
  Anti "uname"   v -> con1P "MeName" (con2P "J" (TH.listP []) 
                                                (con1P "Uid" v))
  Anti "quname"  v -> con1P "MeName" (con2P "J" ('q':v)
                                                (con1P "Uid" v))
  Anti "uid"     v -> con1P "MeName" (con2P "J" (TH.listP []) v)
  Anti "quid"    v -> con1P "MeName" v
  Anti "anti"    v -> con1P "MeAnti" v
  Anti ""        v -> mkvarP v
  Anti t         _ -> unrec t
antiMePat _             = Nothing

antiQuExp :: Quant -> Maybe TH.ExpQ
antiQuExp (QuantAnti anti) = Just $ case anti of
  Anti ""        v -> mkvarE v
  Anti "anti"    v -> [| QuantAnti $(mkvarE v) |]
  Anti t         _ -> unrec t
antiQuExp _                = Nothing

antiQuPat :: Quant -> Maybe TH.PatQ
antiQuPat (QuantAnti anti) = Just $ case anti of
  Anti ""        v -> mkvarP v
  Anti "anti"    v -> con1P "QuantAnti" v
  Anti t         _ -> unrec t
antiQuPat _                = Nothing

antiTvExp :: TyVar -> Maybe TH.ExpQ
antiTvExp (TV lid qual) = do
  anti <- identToAnti lid
  return $ case anti of
    Anti "lid"   v -> [| TV $(mkvarE v) $(toExpQ qual) |]
    Anti "name"  v -> [| TV (Lid $(mkvarE v)) $(toExpQ qual) |]
    Anti ""      v -> mkvarE v
    Anti t       _ -> unrec t

antiTvPat :: TyVar -> Maybe TH.PatQ
antiTvPat (TV lid qual) = do
  anti <- identToAnti lid
  return $ case anti of
    Anti "lid"   v -> con2P "TV" v (toPatQ qual)
    Anti "name"  v -> con2P "TV" (con1P "Lid" v) (toPatQ qual)
    Anti ""      v -> mkvarP v
    Anti t       _ -> unrec t

antiUidExp :: Uid -> Maybe TH.ExpQ
antiUidExp uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> [| Uid $(mkvarE v) |]
    Anti ""      v -> mkvarE v
    Anti t       _ -> unrec t

antiUidPat :: Uid -> Maybe TH.PatQ
antiUidPat uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> con1P "Uid" v
    Anti ""      v -> mkvarP v
    Anti t       _ -> unrec t

antiLidExp :: Lid -> Maybe TH.ExpQ
antiLidExp uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> [| Lid $(mkvarE v) |]
    Anti ""      v -> mkvarE v
    Anti t       _ -> unrec t

antiLidPat :: Lid -> Maybe TH.PatQ
antiLidPat uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> con1P "Lid" v
    Anti ""      v -> mkvarP v
    Anti t       _ -> unrec t

antiQLidExp :: QLid -> Maybe TH.ExpQ
antiQLidExp lid = do
  anti <- identToAnti lid
  return $ case anti of
    Anti "name"  v -> [| J [] (Lid $(mkvarE v)) |]
    Anti "qname" v -> [| qlid $(mkvarE v) |]
    Anti "lid"   v -> [| J [] $(mkvarE v) |]
    Anti "qlid"  v -> mkvarE v
    Anti ""      v -> mkvarE v
    Anti t       _ -> unrec t

antiQLidPat :: QLid -> Maybe TH.PatQ
antiQLidPat lid = do
  anti <- identToAnti lid
  return $ case anti of
    Anti "name"  v -> con2P "J" (TH.listP []) (con1P "Lid" v)
    Anti "qname" v -> con2P "J" ('q':v) (con1P "Lid" v)
    Anti "lid"   v -> con2P "J" (TH.listP []) v
    Anti "qlid"  v -> con2P "J" ('q':v) v
    Anti ""      v -> mkvarP v
    Anti t       _ -> unrec t

antiQUidExp :: QUid -> Maybe TH.ExpQ
antiQUidExp uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> [| J [] (Uid $(mkvarE v)) |]
    Anti "qname" v -> [| quid $(mkvarE v) |]
    Anti "uid"   v -> [| J [] $(mkvarE v) |]
    Anti "quid"  v -> mkvarE v
    Anti ""      v -> mkvarE v
    Anti t       _ -> unrec t

antiQUidPat :: QUid -> Maybe TH.PatQ
antiQUidPat uid = do
  anti <- identToAnti uid
  return $ case anti of
    Anti "name"  v -> con2P "J" (TH.listP []) (con1P "Uid" v)
    Anti "qname" v -> con2P "J" ('q':v) (con1P "Uid" v)
    Anti "uid"   v -> con2P "J" (TH.listP []) v
    Anti "quid"  v -> con2P "J" ('q':v) v
    Anti ""      v -> mkvarP v
    Anti t       _ -> unrec t

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
antiPaExp (PaCon qu (Just (PaAnti (Anti "maybe" v))) b)
                        = Just [| PaCon $(toExpQ qu)
                                        $(mkvarE v)
                                        $(toExpQ b) |]
antiPaExp (PaCon (J [] (Uid ('{':'$':'e':'x':'n':':':v:vs)))
                 (Just (PaCon qu x _)) _)
                        = Just [| PaCon $(toExpQ qu)
                                        $(toExpQ x)
                                        $(mkvarE (init (v:vs))) |]
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
antiPaPat (PaCon qu (Just (PaAnti (Anti "maybe" v))) b)
                        = Just $ mkconP "PaCon"
                            [ toPatQ qu
                            , mkvarP v
                            , toPatQ b ]
antiPaPat (PaCon (J [] (Uid ('{':'$':'e':'x':'n':':':v:vs)))
                 (Just (PaCon qu x _)) _)
                        = Just $ mkconP "PaCon"
                            [ toPatQ qu
                            , toPatQ x
                            , mkvarP (init (v:vs)) ]
antiPaPat _             = Nothing

antiTuExp :: Type () -> Maybe TH.ExpQ
antiTuExp (TyAnti anti) = Just $ case anti of
  Anti "lid"     v -> [| TyCon $(mkvarE v) [] () |]
  Anti "name"    v -> [| TyCon (qlid $(mkvarE v)) [] () |]
  Anti "tv"      v -> [| TyVar $(mkvarE v) |]
  Anti "anti"    v -> [| TyAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiTuExp (TyCon n [TyAnti (Anti "list" v)] i)
  = Just [| TyCon $(toExpQ n) $(mkvarE v) $(toExpQ i) |]
antiTuExp _             = Nothing

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
  Anti "anti"    v -> [| TyTagAnti $(mkvarE v) |]
  Anti ""        v -> mkvarE v
  Anti t         _ -> unrec t
antiTiExp _             = Nothing

antiTiPat :: TyTag -> Maybe TH.PatQ
antiTiPat (TyTagAnti anti) = Just $ case anti of
  Anti "td"      v -> case getTdByName v of
                        Nothing -> fail $
                          "Unrecognized type name: " ++ v
                        Just td -> dataToPatQ (const Nothing) td
  Anti "anti"    v -> con1P "TyTagAnti" (mkvarP v)
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
    ExPack (Just (TyAnti (Anti "maybe" v))) t e
                  -> [| exPack $(mkvarE v) $(toExpQ t) $(loop e) |]
    ExPack mt t e -> [| exPack $(toExpQ mt) $(toExpQ t) $(loop e) |]
    ExCast e (Just (TyAnti (Anti "maybe" v))) t
                  -> [| exCast $(loop e) $(mkvarE v) $(toExpQ t) |]
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
      Anti "anti"    v -> [| exAnti $(mkvarE v) |]
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
    Anti "anti"    v -> exprP (con1P "ExAnti" (mkvarP v))
    Anti ""        v -> mkvarP v
    Anti t         _ -> unrec t
  ExPack (Just (TyAnti (Anti "maybe" v))) t e0
     -> exprP (mkconP "ExPack" [ mkvarP v, toPatQ t, toPatQ e0 ])
  ExCast e0 (Just (TyAnti (Anti "maybe" v))) t
     -> exprP (mkconP "ExCast" [ toPatQ e0, mkvarP v, toPatQ t ])
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

antiDcExp :: Data i => Decl i -> Maybe TH.ExpQ
antiDcExp (DcAnti a) = Just $ case a of
  Anti ""        v -> mkvarE v
  Anti "anti"    v -> [| DcAnti $(mkvarE v) |]
  Anti t         _ -> unrec t
antiDcExp (DcLet loc x (Just (TyAnti (Anti "maybe" v))) e)
                     = Just [| DcLet $(toExpQ loc) $(toExpQ x)
                                     $(mkvarE v) $(toExpQ e) |]
antiDcExp (DcExn loc n (Just (TyAnti (Anti "maybe" v))))
                     = Just [| DcExn $(toExpQ loc) $(toExpQ n) $(mkvarE v) |]
antiDcExp _          = Nothing

antiDcPat :: Data i => Decl i -> Maybe TH.PatQ
antiDcPat (DcAnti a) = Just $ case a of
  Anti ""        v -> mkvarP v
  Anti "anti"    v -> con1P "DcAnti" (mkvarP v)
  Anti t         _ -> unrec t
antiDcPat (DcLet _ x (Just (TyAnti (Anti "maybe" v))) e)
                     = Just (mkconP "DcLet"
                              [ TH.wildP
                              , toPatQ x
                              , mkvarP v
                              , toPatQ e ])
antiDcPat (DcExn loc n (Just (TyAnti (Anti "maybe" v))))
                     = Just $ mkconP "DcExn"
                                [ toPatQ loc, toPatQ n, mkvarP v ]
antiDcPat _          = Nothing

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

