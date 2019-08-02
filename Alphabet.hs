module Alphabet where
import Data.Bits
import Data.Word

type Alphabet = CharSet
type CharSet  = Word32

alphaLength :: Alphabet -> Int
alphaLength = sizeSet

charSet :: Alphabet -> CharSet
charSet = id

firstCharacter :: Char
firstCharacter = 'a'

nthChar :: Int -> Char
nthChar n = toEnum (n+firstCharInt)

firstCharInt = fromEnum firstCharacter

embed :: Char -> CharSet
embed c = bit (fromEnum c - firstCharInt)

removeFromCharSet :: Char -> CharSet -> Maybe CharSet
removeFromCharSet c cs = if cs==cs' then Nothing
                         else Just cs'
                         where cs' = embed c `xor` cs

embedAlphabet :: Char -> Alphabet
embedAlphabet = embed

emptyAlphabet :: Alphabet
emptyAlphabet = emptySet

embedSet :: CharSet -> Alphabet
embedSet = id

emptySet :: CharSet
emptySet = zeroBits

elemSet :: Char -> CharSet -> Bool
elemSet x c = not $ isEmptySet(embed x .&. c)

enumerate :: Alphabet -> [Char]
enumerate = enumerateSet

enumerateSet :: CharSet -> [Char]
enumerateSet cs |  isEmptySet cs
                =  []
                |  otherwise
                =  nthChar n : enumerateSet (clearBit cs n)
                   where n = firstIndex cs

showSet :: CharSet -> String
showSet cs = foldr f "{}" (enumerateSet cs)
             where
             f c "{}"   = ['{',c,'}']
             f c (d:ds) = d:c:',':ds
             f c ""     = "we will not go here!"

showAlphabet :: Alphabet -> String
showAlphabet = showSet

fromList :: [Char] -> CharSet
fromList []     = zeroBits
fromList (x:xs) = embed x .|. fromList xs

(.&&.) :: Alphabet -> Alphabet -> Alphabet
(.&&.) = (.&.)

(.||.) :: Alphabet -> Alphabet -> Alphabet
(.||.) = (.|.)

unionS :: [CharSet] -> CharSet
unionS = foldr (.|.) emptySet

unionA :: [Alphabet] -> Alphabet
unionA = foldr (.||.) emptyAlphabet

isEmptyAlph :: Alphabet -> Bool
isEmptyAlph = isEmptySet

singletonAlpha :: Alphabet -> Bool
singletonAlpha cs = isEmptySet ((cs-1) .&. cs)

isEmptySet :: CharSet -> Bool
isEmptySet xs = xs==emptySet

sizeSet :: CharSet -> Int
sizeSet xs = popCount xs

firstChar, lastChar :: CharSet -> Maybe Char
lastChar  cs  |  isEmptySet cs
              =  Nothing
              |  otherwise
              =  Just $ toEnum $ lastIndex cs + firstCharInt

firstChar cs  |  isEmptySet cs
              =  Nothing
              |  otherwise
              =  Just $ toEnum $ lastIndex cs + firstCharInt

dual :: (a->a->Ordering) -> (a->a->Ordering)
dual co x y = case co x y of { LT -> GT; GT -> LT; EQ -> EQ }

setOrder :: CharSet -> CharSet -> Ordering
setOrder x y =  compare (firstIndex (y .&. z))(firstIndex (x .&. z))
                where
                z  = xor x y

subsetS :: CharSet -> CharSet -> Bool
subsetS cs ds = (cs .&. ds) == cs

strictSubset :: CharSet -> CharSet -> Bool
strictSubset cs ds = cs/=ds && subsetS cs ds

isCanonicalCS :: CharSet -> Bool
isCanonicalCS cs = popCount (cs+1) == 1

pluralCS :: CharSet -> Bool
pluralCS cs = not $ isEmptySet ((cs-1) .&. cs)


lastIndex :: CharSet -> Int
lastIndex 0 = -1
lastIndex 1 = 0
lastIndex n = 1+lastIndex(div n 2)

firstIndex :: CharSet -> Int
firstIndex 0 = 32
firstIndex n | odd n 
             = 0
             | otherwise
             = 1+firstIndex(div n 2)




