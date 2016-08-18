module Util where

(<->) :: Eq a => [a] -> a -> [a]
l <-> a = filter (/= a) l

find :: (a -> Bool) -> [a] -> Maybe a
find p l = case l of
  [] -> Nothing
  h : t -> case p h of
            True -> Just h
            False -> find p t

split :: [a] -> Int -> ([a], [a])
split l n = aux n [] l
  where aux :: Int -> [a] -> [a] -> ([a], [a])
        aux i acc [] = (reverse acc, [])
        aux i acc (h : t) = case i of
                              0 -> (reverse acc, t)
                              _ -> aux (i - 1) (h : acc) t