{-# LANGUAGE
      FlexibleInstances,
      GADTs,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      PatternGuards,
      TemplateHaskell
      #-}
module Message.Quasi (
  msg, Message(), H, V,
) where

import Message.AST
import Message.Parser
import Meta.THHelpers
import Syntax.PprClass
import Util hiding (lift)

import Prelude ()
import qualified Data.Map as M
import Language.Haskell.TH
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax (lift)

msg :: QuasiQuoter
msg  = (newQuasi "msg") { quoteExp = parseMessageQ >=> msgAstToExpQ }

msgAstToExpQ :: Message d -> ExpQ
msgAstToExpQ msg0 = do
  namelist <- sequence
                [ (,) (show z) `liftM` newName ("_v"++show z)
                | z <- [ 1 .. highest msg0 ] ]
  let expQ = translate (M.fromList namelist) msg0
  foldr (\(_, var) -> lamE [varP var]) expQ namelist
  where
  highest :: Message d -> Int
  highest msg1 = case msg1 of
    Words _           -> 0
    Flow msgs         -> maximum (map highest msgs)
    Exact _           -> 0
    Surround _ _ msg' -> highest msg'
    Quote msg'        -> highest msg'
    Stack _ msgs      -> maximum (map highest msgs)
    Table rows        -> maximum (map (highest . snd) rows)
    Indent msg'       -> highest msg'
    Printable _ _     -> 0
    Showable _        -> 0
    AntiMsg _ name    -> case readsPrec 0 name of
      (z,""):_          -> z
      _                 -> 0
  --
  translate :: M.Map String Name -> Message d -> ExpQ
  translate namemap = loop where
    loop :: Message d -> ExpQ
    loop msg1 = case msg1 of
      Words s     -> [| Words $(lift s) |]
      Flow msgs   -> [| Flow $(listE (map loop msgs)) |]
      Exact s     -> [| Exact $(lift s) |]
      Surround s e msg'
                  -> [| Surround $(lift s) $(lift e) $(loop msg') |]
      Quote msg'  -> [| Quote $(loop msg') |]
      Stack sty msgs
                  -> [| Stack $(styleQ sty)
                              $(listE (map loop msgs)) |]
        where styleQ Numbered  = [| Numbered |]
              styleQ Bulleted  = [| Bulleted |]
              styleQ Separated = [| Separated |]
              styleQ Broken    = [| Broken |]
      Table rows  -> [| Table $(listE (map each rows)) |]
        where each (s,msg') = [| ($(lift s), $(loop msg')) |]
      Indent msg' -> [| Indent $(loop msg') |]
      Printable d a
                  -> [| Exact $(lift (show (pprDepth d a))) |]
      Showable a  -> [| Exact $(lift (show a)) |]
      AntiMsg tag name -> case tag of
        "words"   -> [| Words $var |]
        "flow"    -> [| Flow $var |]
        "exact"   -> [| Exact $var |]
        "msg"     -> var
        "ol"      -> [| Stack Numbered $var |]
        "ul"      -> [| Stack Bulleted $var |]
        "br"      -> [| Stack Broken $var |]
        "p"       -> [| Stack Separated $var |]
        "dl"      -> [| Table $var |]
        "indent"  -> [| Indent $var |]
        "show"    -> [| Showable $var |]
        'v':tag'  -> [| $(loop (AntiMsg tag' name)) :: Message V |]
        'h':tag'  -> [| $(loop (AntiMsg tag' name)) :: Message H |]
        'q':tag'  -> [| Quote $(loop (AntiMsg tag' name)) |]
        ""        -> [| Printable 0 $var |]
        _ | [(d,"")] <- (reads tag :: [(Int,String)])
                  -> [| Printable d $var |]
        _         -> fail $
          "Unknown message antiquote tag: ‘" ++ tag ++ "’"
        where var = varE (M.findWithDefault (mkName name) name namemap)

