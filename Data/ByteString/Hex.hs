module Data.ByteString.Hex
    ( showHexByte
    , showHexBytes
    , parseHexDigit
    , parseHexByte
    , parseHexDigits
    ) where

import           Control.Lens.Operators
import qualified Data.ByteString as SBS
import qualified Data.Char as Char
import           Data.Word (Word8)
import           Text.Printf (printf)

showHexByte :: Word8 -> String
showHexByte = printf "%02X"

showHexBytes :: SBS.ByteString -> String
showHexBytes = concatMap showHexByte . SBS.unpack

chunks :: Int -> [a] -> Either String [[a]]
chunks _ [] = Right []
chunks n xs
    | length firstChunk == n = chunks n rest <&> (firstChunk :)
    | otherwise = Left $ unwords ["Expecting chunks of size", show n, "found", show (length firstChunk)]
    where
        (firstChunk, rest) = splitAt n xs

parseHexDigit :: Char -> Either String Word8
parseHexDigit x
    | Char.isHexDigit x = Right (fromIntegral (Char.digitToInt x))
    | otherwise = Left $ "Expecting digit, found " ++ show x

parseHexByte :: String -> Either String Word8
parseHexByte [x,y] =
    (+)
    <$> (parseHexDigit x <&> (16 *))
    <*> parseHexDigit y
parseHexByte other =
    Left $ unwords ["Expecting two hex digits, found", show (length other), "characters"]

parseHexDigits :: String -> Either String SBS.ByteString
parseHexDigits str =
    chunks 2 str >>= mapM parseHexByte <&> SBS.pack
