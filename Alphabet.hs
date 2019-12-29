module Alphabet (
  Alphabet, emptyAlpha, isEmptyAlpha, singularAlpha, pluralAlpha,
  elemAlpha, subAlpha, strictSubAlpha, freshChar,
  char2Alpha, string2Alpha, alpha2String, alphaLength,
  unionA, (.||.), (.&&.), (.\\.)
  -- charSet,
  -- emptySet, isEmptySet, embed, embedSet, elemSet, sizeSet, pluralCS,
  -- unionS, subsetS, strictSubset, setOrder, showSet, enumerateSet, fromList
  ) where

import Data.Bits
import Data.Word

type Alphabet = Word32

firstCharacter :: Char
firstCharacter = 'a'

nthChar :: Int -> Char
nthChar n = toEnum (n+firstCharInt)

firstCharInt :: Int
firstCharInt = fromEnum firstCharacter

char2Alpha :: Char -> Alphabet
char2Alpha c = bit (fromEnum c - firstCharInt)

emptyAlpha :: Alphabet
emptyAlpha  =  zeroBits

elemAlpha :: Char -> Alphabet -> Bool
elemAlpha x c = not $ isEmptyAlpha (char2Alpha x .&. c)

alpha2String:: Alphabet -> [Char]
alpha2String cs  |  isEmptyAlpha cs
                 =  []
                 |  otherwise
                 =  nthChar n : alpha2String (clearBit cs n)
                    where n = firstIndex cs

showAlpha :: Alphabet -> String
showAlpha cs = foldr f "{}" (alpha2String cs)
               where
               f c "{}"   = ['{',c,'}']
               f c (d:ds) = d:c:',':ds
               f c ""     = "we will not go here!"

string2Alpha :: [Char] -> Alphabet
string2Alpha []     = zeroBits
string2Alpha (x:xs) = char2Alpha x .|. string2Alpha xs

(.&&.) :: Alphabet -> Alphabet -> Alphabet
(.&&.) = (.&.)

(.||.) :: Alphabet -> Alphabet -> Alphabet
(.||.) = (.|.)

(.\\.) :: Alphabet -> Alphabet -> Alphabet
a1 .\\. a2 = a1 .&&. complement a2

unionA :: [Alphabet] -> Alphabet
unionA = foldr (.||.) emptyAlpha

isEmptyAlpha :: Alphabet -> Bool
isEmptyAlpha xs  =  xs == emptyAlpha

singularAlpha :: Alphabet -> Bool
singularAlpha cs = isEmptyAlpha ((cs-1) .&. cs)

alphaLength :: Alphabet -> Int
alphaLength xs = popCount xs

firstChar, lastChar :: Alphabet -> Maybe Char
lastChar  cs  |  isEmptyAlpha cs
              =  Nothing
              |  otherwise
              =  Just $ toEnum $ lastIndex cs + firstCharInt

firstChar cs  |  isEmptyAlpha cs
              =  Nothing
              |  otherwise
              =  Just $ toEnum $ lastIndex cs + firstCharInt

freshChar :: Alphabet -> Char
freshChar a = maybe 'a' succ $ lastChar a

subAlpha :: Alphabet -> Alphabet -> Bool
subAlpha cs ds = (cs .&. ds) == cs

strictSubAlpha :: Alphabet -> Alphabet -> Bool
strictSubAlpha cs ds = cs/=ds && subAlpha cs ds

isCanonicalAlpha :: Alphabet -> Bool
isCanonicalAlpha cs = popCount (cs+1) == 1

pluralAlpha :: Alphabet -> Bool
pluralAlpha cs = not $ isEmptyAlpha ((cs-1) .&. cs)

lastIndex :: Alphabet -> Int
lastIndex 0 = -1
lastIndex 1 = 0
lastIndex n = 1+lastIndex(div n 2)

firstIndex :: Alphabet -> Int
firstIndex 0 = 32
firstIndex n | odd n
             = 0
             | otherwise
             = 1+firstIndex(div n 2)
