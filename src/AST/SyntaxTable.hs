module AST.SyntaxTable where

import Meta.THHelpers
import AST.Anti
import AST.Notable
import AST.Ident
import AST.Kind
import AST.Type
import AST.Lit
import AST.Patt
import AST.Expr
import AST.Decl

import qualified Data.Map as M
import qualified Language.Haskell.TH as TH

litAntis, pattAntis,
  exprAntis, bindingAntis, caseAltAntis, fieldAntis,
  typeAntis, tyPatAntis, quantAntis, qExpAntis, tyVarAntis,
  declAntis, tyDecAntis, absTyAntis, modExpAntis,
  sigExpAntis, sigItemAntis,
  lidAntis, uidAntis,
  typIdAntis, varIdAntis, conIdAntis, modIdAntis, sigIdAntis,
  qlidAntis, quidAntis,
  qtypIdAntis, qvarIdAntis, qconIdAntis, qmodIdAntis, qsigIdAntis,
  idAntis, noAntis
    :: AntiDict

litAntis
  = "lit"    =:  Nothing
  & "str"    =:< 'LtStr
  & "int"    =:< 'LtInt
  & "flo"    =:< 'LtFloat
  & "float"  =:< 'LtFloat
  & "char"   =:< 'LtChar
  & "antiL"  =:< 'LtAnti
pattAntis
  = "patt"   =:! Nothing
  & "anti"   =:< 'PaAnti
exprAntis
  = "expr"   =:! Nothing
  & "anti"   =:< 'ExAnti
bindingAntis
  = "bind"   =:! Nothing
  & "antiB"  =:< 'BnAnti
caseAltAntis
  = "case"   =:  Nothing
  & "antiC"  =:< 'CaAnti
fieldAntis
  = "field"  =:  Nothing
  & "antiF"  =:< 'FdAnti
typeAntis
  = "type"   =:! Nothing
  & "anti"   =:< 'TyAnti
tyPatAntis
  = "typat"  =:! Nothing
  & "antiP"  =:< 'TpAnti
quantAntis
  = "quant"  =:  Nothing
  & "antiQ"  =:< 'QuantAnti
qExpAntis
  = "qexp"   =:! Nothing
  & "qlit"   =:< 'QeLit
  & "qvar"   =:< 'QeVar
  & "anti"   =:< 'QeAnti
tyVarAntis
  = "tyvar"  =:! Nothing
  & "anti"   =:< 'TVAnti
declAntis
  = "decl"   =:! Nothing
  & "anti"   =:< 'DcAnti
tyDecAntis
  = "tydec"  =:! Nothing
  & "anti"   =:< 'TdAnti
absTyAntis
  = "absty"  =:! Nothing
  & "anti"   =:< 'AbsTyAnti
modExpAntis
  = "mod"    =:! Nothing
  & "anti"   =:< 'MeAnti
sigExpAntis
  = "sig"    =:! Nothing
  & "anti"   =:< 'SeAnti
sigItemAntis
  = "sgitem" =:! Nothing
  & "anti"   =:< 'SgAnti
lidAntis
  = "lid"    =:  Nothing
  & "name"   =:•• (['ident], ['Lid])
  & "antiLid"=:< 'LidAnti
uidAntis
  = "uid"    =:  Nothing
  & "uname"  =:•• (['ident], ['Uid])
  & "antiUid"=:< 'LidAnti
typIdAntis
  = "tid"    =:  Nothing
  & "lid"    =:< 'TypId
  & "lname"  =:•• (['ident], ['TypId, 'Lid])
  & "antiTI" =:• ['TypId, 'LidAnti]
varIdAntis
  = "vid"    =:  Nothing
  & "lid"    =:< 'VarId
  & "lname"  =:•• (['ident], ['VarId, 'Lid])
  & "antiVI" =:• ['VarId, 'LidAnti]
conIdAntis
  = "cid"    =:  Nothing
  & "uid"    =:< 'ConId
  & "uname"  =:•• (['ident], ['ConId, 'Uid])
  & "antiCI" =:• ['ConId, 'UidAnti]
modIdAntis
  = "mid"    =:  Nothing
  & "uid"    =:< 'ModId
  & "uname"  =:•• (['ident], ['SigId, 'Uid])
  & "antiMI" =:• ['ModId, 'UidAnti]
sigIdAntis
  = "sid"    =:  Nothing
  & "uid"    =:< 'SigId
  & "uname"  =:•• (['ident], ['SigId, 'Uid])
  & "antiSI" =:• ['SigId, 'UidAnti]
qlidAntis
  = "qlid"   =:  Nothing
  & "qname"  =:  appFun 'qident -- error in pattern context
quidAntis
  = "quid"   =:  Nothing
  & "quname" =:  appFun 'qident -- error in pattern context
qtypIdAntis
  = "qtid"   =:  Nothing
  & "qname"  =:  appFun 'qident -- error in pattern context
qvarIdAntis
  = "qvid"   =:  Nothing
  & "qname"  =:  appFun 'qident -- error in pattern context
qconIdAntis
  = "qcid"   =:  Nothing
  & "quname" =:  appFun 'qident -- error in pattern context
qmodIdAntis
  = "qmid"   =:  Nothing
  & "quname" =:  appFun 'qident -- error in pattern context
qsigIdAntis
  = "qsid"   =:  Nothing
  & "quname" =:  appFun 'qident -- error in pattern context
idAntis
  = "id"     =:  Nothing
noAntis
  = M.empty

appFun :: ToSyntax b => TH.Name -> Maybe (String -> TH.Q b)
appFun n = Just (\v -> varS n [varS v []])

syntaxTable :: SyntaxTable
syntaxTable =
  [ ''Prog    =:: 'Prog                       !: 'newN       >: (''Tag, [0])
  , ''Lit     =:: 'LtAnti    $: 'litAntis
  , ''Patt    =:: 'PaAnti    $: 'pattAntis    !: 'newPatt    >: (''Tag, [0])
  , ''Expr    =:: 'ExAnti    $: 'exprAntis    !: 'newExpr    >: (''Tag, [0])
  , ''Binding =:: 'BnAnti    $: 'bindingAntis !: 'newBinding >: (''Tag, [0])
  , ''CaseAlt =:: 'CaAnti    $: 'caseAltAntis !: 'newCaseAlt >: (''Tag, [0])
  , ''Field   =:: 'FdAnti    $: 'fieldAntis   !: 'newField   >: (''Tag, [0])
  , ''Type    =:: 'TyAnti    $: 'typeAntis    !: 'newN
  , ''TyPat   =:: 'TpAnti    $: 'tyPatAntis   !: 'newN
  , ''Quant   =:: 'QuantAnti $: 'quantAntis
  , ''QExp    =:: 'QeAnti    $: 'qExpAntis    !: 'newN
  , ''TyVar   =:: 'TVAnti    $: 'tyVarAntis
  , ''Decl    =:: 'DcAnti    $: 'declAntis    !: 'newDecl    >: (''Tag, [0])
  , ''TyDec   =:: 'TdAnti    $: 'tyDecAntis   !: 'newN
  , ''AbsTy   =:: 'AbsTyAnti $: 'absTyAntis   !: 'newN
  , ''ModExp  =:: 'MeAnti    $: 'modExpAntis  !: 'newModExp  >: (''Tag, [0])
  , ''SigExp  =:: 'SeAnti    $: 'sigExpAntis  !: 'newSigExp  >: (''Tag, [0])
  , ''SigItem =:: 'SgAnti    $: 'sigItemAntis !: 'newSigItem >: (''Tag, [0])
  , ''Lid     =:: 'LidAnti   $: 'lidAntis
  , ''Uid     =:: 'UidAnti   $: 'uidAntis
  , ''TypId   =:: ['TypId, 'LidAnti] $: 'typIdAntis
  , ''VarId   =:: ['VarId, 'LidAnti] $: 'varIdAntis
  , ''ConId   =:: ['ConId, 'UidAnti] $: 'conIdAntis
  , ''ModId   =:: ['ModId, 'UidAnti] $: 'modIdAntis
  , ''SigId   =:: ['SigId, 'UidAnti] $: 'sigIdAntis
  , ''QLid    =:: '()
  , ''QUid    =:: '()
  , ''QTypId  =:: '()
  , ''QVarId  =:: '()
  , ''QConId  =:: '()
  , ''QModId  =:: '()
  , ''QSigId  =:: '()
  , ''Ident   =:: '()
  ]

