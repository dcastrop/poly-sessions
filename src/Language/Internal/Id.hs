{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Internal.Id
  ( Name
  , Id
  , mkName
  , mkId )
where

import Data.Text.Prettyprint.Doc ( Pretty, pretty )

newtype Name = Name { unName :: NameRepr () }
deriving instance Eq Name
deriving instance Ord Name

mkName :: String -> Name
mkName s = Name NameRepr { nameId = (), nameLbl = s }

instance Pretty Name where
  pretty = pretty . unName

newtype Id   = Id   { unId :: NameRepr Integer }
deriving instance Eq Id
deriving instance Ord Id

mkId :: Integer -> String -> Id
mkId i s = Id NameRepr { nameId = i, nameLbl = s }

instance Pretty Id where
  pretty = pretty . unId

data NameRepr a = NameRepr { nameId  :: a
                           , nameLbl :: String }
deriving instance Eq  a => Eq  (NameRepr a)
deriving instance Ord a => Ord (NameRepr a)

instance Pretty (NameRepr a) where
  pretty (nameLbl -> l) = pretty l

