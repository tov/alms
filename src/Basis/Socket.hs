{-# OPTIONS_GHC -fcontext-stack=50 -fno-warn-orphans #-}
{-# LANGUAGE
      DeriveDataTypeable,
      StandaloneDeriving
  #-}
module Basis.Socket ( entries ) where

import Data.Data as Data
import Foreign.C.Types (CInt)
import qualified Network.Socket as S

import Basis.IO ()
import BasisUtils
import Value
import Ppr (text)

instance Valuable S.Socket where
  veq = (==)
  vpprPrec _ _ = text "#<socket>"

instance Valuable S.Family where
  veq      = (==)
  vpprPrec _ = text . show
  vinj     = vinjData
  vprjM    = vprjDataM
deriving instance Typeable S.Family
deriving instance Data S.Family

instance Valuable S.ShutdownCmd where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Eq S.ShutdownCmd
deriving instance Show S.ShutdownCmd
deriving instance Data S.ShutdownCmd

instance Valuable S.SocketType where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.SocketType

instance Valuable S.AddrInfoFlag where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.AddrInfoFlag

instance Valuable S.PortNumber where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM

portNumberType :: DataType
portNumberType  = mkDataType "Network.Socket.PortNumber" [portNumConstr]
portNumConstr  :: Constr
portNumConstr   = mkConstr portNumberType "PortNum" [] Prefix

fakePortNumCon :: Integer -> S.PortNumber
fakePortNumCon  = fromIntegral
fakePortNumSel :: S.PortNumber -> Integer
fakePortNumSel  = toInteger

instance Data S.PortNumber where
  gfoldl f z portNum = z fakePortNumCon `f` (fakePortNumSel portNum)
  toConstr (S.PortNum _)  = portNumConstr
  gunfold k z c = case constrIndex c of
                    1 -> k (z fakePortNumCon)
                    _ -> error "gunfold"
  dataTypeOf _ = portNumberType

instance Data.Data CInt where
  toConstr x = mkIntConstr cIntType (fromIntegral x)
  gunfold _ z c = case constrRep c of
                    (IntConstr x) -> z (fromIntegral x)
                    _ -> error "gunfold"
  dataTypeOf _ = cIntType
cIntType :: DataType
cIntType  = mkIntType "Foreign.C.Types.CInt"

instance Valuable S.SockAddr where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.SockAddr

instance Valuable S.AddrInfo where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.AddrInfo

entries :: [Entry]
entries  = [
    typ "portNumber = PortNum of int",
    typ "socket",
    typ (enumTypeDecl S.AF_INET),
    typ (enumTypeDecl S.Stream),
    typ "protocolNumber = int",
    typ "hostAddress  = int",
    typ "flowInfo     = int",
    typ "hostAddress6 = int * int * int * int",
    typ "scopeID      = int",
    typ "sockAddr = SockAddrInet of portNumber * hostAddress"
        "         | SockAddrInet6 of"
        "             portNumber * flowInfo * hostAddress6 * scopeID"
        "         | SockAddrUnix of string",
    typ (enumTypeDecl S.AI_ALL),
    typ (enumTypeDecl S.ShutdownSend),
    typ "addrInfo = AddrInfo of"
        "  addrInfoFlag list * family * socketType *"
        "  protocolNumber * sockAddr * string option",
    typ "hostName = string",
    typ "serviceName = string",

    val "inaddr_any" -: "hostAddress"
      -= S.iNADDR_ANY,
    val "defaultProtocol" -: "protocolNumber"
      -= S.defaultProtocol,
    val "defaultHints" -: "addrInfo"
      -= S.defaultHints {
           S.addrAddress  = S.SockAddrInet S.aNY_PORT S.iNADDR_ANY,
           S.addrCanonName = Nothing
         },

    fun "getAddrInfo"
      -: ("addrInfo option -> hostName option -> " ++
          "serviceName option -> addrInfo list")
      -= S.getAddrInfo,
    fun "inet_addr" -: "string -> hostAddress"
      -= S.inet_addr,

    fun "socket" -: "family -> socketType -> protocolNumber -> socket"
      -= S.socket,
    fun "bind"   -: "socket -> sockAddr -> unit"
      -= S.bindSocket,
    fun "connect"   -: "socket -> sockAddr -> unit"
      -= S.connect,
    fun "listen" -: "socket -> int -> unit"
      -= S.listen,
    fun "accept" -: "socket -> socket * sockAddr"
      -= S.accept,
    fun "send" -: "socket -> string -> int"
      -= \sock str -> S.send sock str,
    fun "recv" -: "socket -> int -> string"
      -= \sock len -> S.recv sock len,
    fun "shutdown" -: "socket -> shutdownCmd -> unit"
      -= S.shutdown,
    fun "close" -: "socket -> unit"
      -= S.sClose,

    fun "isReadable" -: "socket -> bool"
      -= S.sIsReadable,
    fun "isWritable" -: "socket -> bool"
      -= S.sIsWritable
  ]

