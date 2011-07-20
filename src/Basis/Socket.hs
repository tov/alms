module Basis.Socket ( entries ) where

import Data.Data as Data
import Foreign.C.Types (CInt)
import qualified Network.Socket as S

import Basis.IO ()
import BasisUtils
import AST
import Value
import qualified Data.Loc

instance Valuable S.Socket where
  veq = (==)
  vppr _ = text "#<socket>"

instance Valuable S.Family where
  veq      = (==)
  vppr     = text . show
  vinj     = vinjData
  vprjM    = vprjDataM
deriving instance Typeable S.Family
deriving instance Data S.Family

instance Valuable S.ShutdownCmd where
  veq        = (==)
  vppr       = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Eq S.ShutdownCmd
deriving instance Show S.ShutdownCmd
deriving instance Data S.ShutdownCmd

instance Valuable S.SocketType where
  veq        = (==)
  vppr       = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.SocketType

instance Valuable S.AddrInfoFlag where
  veq        = (==)
  vppr       = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.AddrInfoFlag

instance Valuable S.PortNumber where
  veq        = (==)
  vppr       = text . show
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
  toConstr x = mkIntegralConstr cIntType (fromIntegral x :: CInt)
  gunfold _ z c = case constrRep c of
                    (IntConstr x) -> z (fromIntegral x)
                    _ -> error "gunfold"
  dataTypeOf _ = cIntType
cIntType :: DataType
cIntType  = mkIntType "Foreign.C.Types.CInt"

instance Valuable S.SockAddr where
  veq        = (==)
  vppr       = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.SockAddr

instance Valuable S.AddrInfo where
  veq        = (==)
  vppr       = text . show
  vinj       = vinjData
  vprjM      = vprjDataM
deriving instance Data S.AddrInfo

entries :: [Entry Raw]
entries  = [
    dec [sgQ| type portNumber = PortNum of int |],
    dec [sgQ| type socket |],
    typ (enumTypeDecl S.AF_INET),
    typ (enumTypeDecl S.Stream),
    dec [sgQ| type protocolNumber = int |],
    dec [sgQ| type hostAddress  = int |],
    dec [sgQ| type flowInfo     = int |],
    dec [sgQ| type hostAddress6 = int * int * int * int |],
    dec [sgQ| type scopeID      = int |],
    dec [sgQ| type sockAddr
                 = SockAddrInet of portNumber * hostAddress
                 | SockAddrInet6 of
                     portNumber * flowInfo * hostAddress6 * scopeID
                 | SockAddrUnix of string |],
    typ (enumTypeDecl S.AI_ALL),
    typ (enumTypeDecl S.ShutdownSend),
    dec [sgQ| type addrInfo
                = AddrInfo of
                    addrInfoFlag list * family * socketType *
                    protocolNumber * sockAddr * string option |],
    dec [sgQ| type hostName = string |],
    dec [sgQ| type serviceName = string |],

    val "inaddr_any" -: [ty| hostAddress |]
      -= S.iNADDR_ANY,
    val "defaultProtocol" -: [ty| protocolNumber |]
      -= S.defaultProtocol,
    val "defaultHints" -: [ty| addrInfo |]
      -= S.defaultHints {
           S.addrAddress  = S.SockAddrInet S.aNY_PORT S.iNADDR_ANY,
           S.addrCanonName = Nothing
         },

    fun "getAddrInfo"
      -: [ty| addrInfo option -> hostName option ->
                serviceName option -> addrInfo list |]
      -= S.getAddrInfo,
    fun "inet_addr" -: [ty| string -> hostAddress |]
      -= S.inet_addr,

    fun "socket" -: [ty| family -> socketType -> protocolNumber -> socket |]
      -= S.socket,
    fun "bind"   -: [ty| socket -> sockAddr -> unit |]
      -= S.bindSocket,
    fun "connect"   -: [ty| socket -> sockAddr -> unit |]
      -= S.connect,
    fun "listen" -: [ty| socket -> int -> unit |]
      -= S.listen,
    fun "accept" -: [ty| socket -> socket * sockAddr |]
      -= S.accept,
    fun "send" -: [ty| socket -> string -> int |]
      -= \sock str -> S.send sock str,
    fun "recv" -: [ty| socket -> int -> string |]
      -= \sock len -> S.recv sock len,
    fun "shutdown" -: [ty| socket -> shutdownCmd -> unit |]
      -= S.shutdown,
    fun "close" -: [ty| socket -> unit |]
      -= S.sClose,

    fun "isReadable" -: [ty| socket -> bool |]
      -= S.sIsReadable,
    fun "isWritable" -: [ty| socket -> bool |]
      -= S.sIsWritable
  ]

