{-# OPTIONS -fcontext-stack=50 -fno-warn-orphans #-}
{-# LANGUAGE
      DeriveDataTypeable,
      StandaloneDeriving
  #-}
module Basis.Socket ( entries ) where

import Data.Typeable (Typeable)
import Data.Word (Word32)
import Foreign.C.Types (CInt)
import qualified Network.Socket as S

import Basis.IO ()
import BasisUtils
import Dynamics
import Ppr (text)

instance Valuable S.Socket where
  veq = (==)
  vpprPrec _ _ = text "#<socket>"

instance Valuable S.Family where
  veq      = (==)
  vpprPrec _ = text . show
  vinj     = vinjEnum
  vprjM    = vprjEnum
deriving instance Typeable S.Family

instance Valuable S.SocketType where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjEnum
  vprjM      = vprjEnum

instance Valuable S.AddrInfoFlag where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinjEnum
  vprjM      = vprjEnum

instance Valuable S.PortNumber where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable Word32 where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable CInt where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable S.SockAddr where
  veq        = (==)
  vpprPrec _ = text . show
  vinj (S.SockAddrInet portNumber hostAddress)
    = vinjStruct "SockAddrInet"
        [vinj (toInteger portNumber),
         vinj (toInteger hostAddress)]
  vinj (S.SockAddrInet6 portNumber flowInfo (ha1, ha2, ha3, ha4) scopeID)
    = vinjStruct "SockAddrInet6"
        [vinj (toInteger portNumber),
         vinj (toInteger flowInfo),
         vinjProd (map (vinj . toInteger) [ha1, ha2, ha3, ha4]),
         vinj (toInteger scopeID)]
  vinj (S.SockAddrUnix s)
    = vinjStruct "SockAddrUnix" [vinj s]
  vprjM v = do
    (name, [fields]) <- vprjStruct 1 v
    case name of
      "SockAddrInet" -> do
        [f1, f2] <- vprjProd 2 fields
        v1 <- vprjM f1
        v2 <- vprjM f2
        return (S.SockAddrInet v1 v2)
      "SockAddrInet6" -> do
        [f1, f2, f3, f4] <- vprjProd 4 fields
        v1 <- vprjM f1
        v2 <- vprjM f2
        [v31, v32, v33, v34] <- vprjProd 5 f3 >>= mapM vprjM
        v4 <- vprjM f4
        return (S.SockAddrInet6 v1 v2 (v31, v32, v33, v34) v4)
      _              -> do
        [f1] <- vprjProd 1 fields
        v1   <- vprjM f1
        return (S.SockAddrUnix v1)

instance Valuable S.AddrInfo where
  veq        = (==)
  vpprPrec _ = text . show
  vinj (S.AddrInfo f1 f2 f3 f4 f5 f6)
             = vinjStruct "AddrInfo"
                          [vinj f1, vinj f2, vinj f3, vinj f4, vinj f5, vinj f6]
  vprjM v    = do
    (_, [f1, f2, f3, f4, f5, f6]) <- vprjStruct 6 v
    v1 <- vprjM f1
    v2 <- vprjM f2
    v3 <- vprjM f3
    v4 <- vprjM f4
    v5 <- vprjM f5
    v6 <- vprjM f6
    return (S.AddrInfo v1 v2 v3 v4 v5 v6)

entries :: [Entry]
entries  = [
    typeC "socket",
    typeC "family = AF_UNSPEC"
           "      | AF_UNIX"
           "      | AF_INET"
           "      | AF_INET6"
           "      | AF_SNA"
           "      | AF_DECnet"
           "      | AF_APPLETALK"
           "      | AF_ROUTE"
           "      | AF_X25"
           "      | AF_AX25"
           "      | AF_IPX"
           "      | AF_NETROM"
           "      | AF_BRIDGE"
           "      | AF_ATMPVC"
           "      | AF_ROSE"
           "      | AF_NETBEUI"
           "      | AF_SECURITY"
           "      | AF_PACKET"
           "      | AF_ASH"
           "      | AF_ECONET"
           "      | AF_ATMSVC"
           "      | AF_IRDA"
           "      | AF_PPPOX"
           "      | AF_WANPIPE"
           "      | AF_BLUETOOTH",
    typeC "socketType = NoSocketType"
           "          | Stream"
           "          | Datagram"
           "          | Raw"
           "          | RDM"
           "          | SeqPacket",
    typeC "protocolNumber = int",
    typeC "portNumber   = int",
    typeC "hostAddress  = int",
    typeC "flowInfo     = int",
    typeC "hostAddress6 = int * int * int * int",
    typeC "scopeID      = int",
    typeC "sockAddr = SockAddrInet of portNumber * hostAddress"
          "         | SockAddrInet6 of"
          "             portNumber * flowInfo * hostAddress6 * scopeID"
          "         | SockAddrUnix of string",
    typeC "addrInfoFlag = AI_ADDRCONFIG"
          "             | AI_ALL"
          "             | AI_CANONNAME"
          "             | AI_NUMERICHOST"
          "             | AI_NUMERICSERV"
          "             | AI_PASSIVE"
          "             | AI_V4MAPPED",
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
      -= S.recv
  ]

