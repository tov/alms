{-# LANGUAGE GADTs #-}
module Message.Render (
  module Syntax.PprClass
) where

import Syntax.PprClass
import Message.AST

-- | Context for message rendering
data RenderContext
  = RenderContext {
      rcDetail  :: Int,
      rcQtLevel :: Int,
      rcLeft    :: Doc,
      rcRight   :: Doc
    }

rc0 :: RenderContext
rc0  = RenderContext (-1) 0 mempty mempty

getQuotes :: RenderContext -> (String, String)
getQuotes cxt =
  if even (rcQtLevel cxt)
#ifdef UNICODE
    then ("‘", "’")
    else ("“", "”")
#else
    then ("'", "'")
    else ("\"", "\"")
#endif

bullet :: Char
#if UNICODE
bullet  = '•'
#else
bullet  = '-'
#endif


incQuotes :: RenderContext -> RenderContext
incQuotes cxt = cxt { rcQtLevel = rcQtLevel cxt + 1 }

clearLeft, clearRight :: RenderContext -> RenderContext
clearLeft cxt  = cxt { rcLeft = mempty }
clearRight cxt = cxt { rcRight = mempty }

addQuotes :: RenderContext -> Doc -> Doc
addQuotes cxt doc = rcLeft cxt <> doc <> rcRight cxt

renderAntiMsg     :: String -> String -> Doc
renderAntiMsg  t a = text "${" <> text t <> colon <> text a <> char '}'

renderMessageH :: RenderContext -> Message H -> [Doc]
renderMessageH cxt msg0 = case msg0 of
  Words s     -> renderMessageH cxt (Flow (map Exact (words s)))
  Exact s     -> [addQuotes cxt (text s)]
  Flow []     -> [addQuotes cxt mempty]
  Flow [msg'] -> renderMessageH cxt msg'
  Flow (m:ms) -> renderMessageH (clearRight cxt) m ++
                 concatMap (renderMessageH cxt') (init ms) ++
                 renderMessageH (clearLeft cxt) (last ms)
     where cxt' = clearRight (clearLeft cxt)
  Surround s e msg'
              -> renderMessageH cxt' {
                   rcLeft  = rcLeft cxt <> text s,
                   rcRight = text e <> rcRight cxt
                 } msg'
    where cxt'   = clearRight (clearLeft cxt)
  Quote msg'  -> renderMessageH cxt' (Surround s e msg')
    where (s, e) = getQuotes cxt
          cxt'   = incQuotes cxt
  Printable d a -> [addQuotes cxt (pprDepth d' a)]
    where d' = if d == 0 then rcDetail cxt else d
  Showable a  -> [addQuotes cxt (text (show a))]
  AntiMsg t a -> [addQuotes cxt (renderAntiMsg t a)]

renderMessage :: RenderContext -> Message d -> Doc
renderMessage cxt msg0 = case msg0 of
  Words s     -> fsep $ renderMessageH cxt (Words s)
  Flow s      -> fsep $ renderMessageH cxt (Flow s)
  Exact s     -> text s
  Surround s e msg'
              -> text s <> renderMessage cxt msg' <> text e
  Quote msg'  -> renderMessage cxt' (Surround s e msg')
    where (s, e) = getQuotes cxt
          cxt'   = incQuotes cxt
  Stack sty msgs -> case sty of
    Numbered  -> vcat [ integer i <> char '.' <+>
                        text (replicate (dent - length (show i)) ' ') <>
                        nest (dent + 2) (renderMessage cxt msg')
                      | msg' <- msgs
                      | i    <- [ 1 .. ] ]
      where len  = length msgs
            dent = length (show len)
    Bulleted  -> vcat [ space <> char bullet <+> nest 3 (renderMessage cxt msg')
                      | msg' <- msgs ]
    Separated -> vcat (punctuate (char '\n')
                                 (map (renderMessage cxt) msgs))
    Broken    -> vcat (map (renderMessage cxt) msgs)
  Table rows  -> vcat [ text label <+>
                        text (replicate (dent - length label) ' ') <>
                        nest (dent + 1) (renderMessage cxt msg')
                      | (label, msg') <- rows ]
    where dent = maximum (map (length . fst) rows)
  Indent msg' -> text "    " <>
                 nest 4 (renderMessage cxt msg')
  Printable d a -> pprDepth d' a
    where d' = if d == 0 then rcDetail cxt else d
  Showable a  -> text (show a)
  AntiMsg t a -> renderAntiMsg t a

instance Ppr (Message d)  where ppr = renderMessage rc0
instance Show (Message d) where showsPrec = showFromPpr

