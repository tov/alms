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
portNumConstr :: Constr
portNumConstr = mkConstr portNumberType "PortNum" [] Prefix

instance Data S.PortNumber where
  gfoldl f z (S.PortNum x) = z S.PortNum `f` x
  toConstr (S.PortNum _)  = portNumConstr
  gunfold k z c = case constrIndex c of
                    1 -> k (z S.PortNum)
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
    typeC "portNumber = PortNum of int",
    typeC "socket",
    typeC (enumTypeDecl S.AF_INET),
    typeC (enumTypeDecl S.Stream),
    typeC "protocolNumber = int",
    typeC "hostAddress  = int",
    typeC "flowInfo     = int",
    typeC "hostAddress6 = int * int * int * int",
    typeC "scopeID      = int",
    typeC "sockAddr = SockAddrInet of portNumber * hostAddress"
          "         | SockAddrInet6 of"
          "             portNumber * flowInfo * hostAddress6 * scopeID"
          "         | SockAddrUnix of string",
    typeC (enumTypeDecl S.AI_ALL),
    typeC "addrInfo = AddrInfo of"
          "  addrInfoFlag list * family * socketType *"
          "  protocolNumber * sockAddr * string option",
    typeC "hostName = string",
    typeC "serviceName = string",

    val "defaultProtocol" -: "protocolNumber" -: ""
      -= S.defaultProtocol,

    fun "getAddrInfo"
      -: ("addrInfo option -> hostName option -> " ++
          "serviceName option -> addrInfo list")
      -: ""
      -= S.getAddrInfo,
    fun "socket" -: "family -> socketType -> protocolNumber -> socket"
                 -: ""
      -= S.socket,
    fun "bind"   -: "socket -> sockAddr -> unit" -: ""
      -= S.bindSocket,
    fun "connect"   -: "socket -> sockAddr -> unit" -: ""
      -= S.connect,
    fun "socketToHandle" -: "socket -> IO.ioMode -> IO.handle" -: ""
      -= S.socketToHandle,
    fun "inet_addr" -: "string -> hostAddress" -: ""
      -= S.inet_addr,
    fun "send" -: "socket -> string -> int" -: ""
      -= S.send,
    fun "recv" -: "socket -> int -> string" -: ""
      -= S.recv,
    fun "listen" -: "socket -> int -> unit" -: ""
      -= S.listen,
    fun "accept" -: "socket -> socket * sockAddr" -: ""
      -= S.accept
  ]

