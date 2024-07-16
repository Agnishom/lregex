module ExtractedNaive where

import qualified Prelude

length :: (([]) a1) -> Prelude.Int
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

nth_error :: (([]) a1) -> Prelude.Int -> Prelude.Maybe a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) x _ -> Prelude.Just x})
    (\n0 ->
    case l of {
     ([]) -> Prelude.Nothing;
     (:) _ l0 -> nth_error l0 n0})
    n

data LRegex a =
   Epsilon
 | CharClass (a -> Prelude.Bool)
 | Concat (LRegex a) (LRegex a)
 | Union (LRegex a) (LRegex a)
 | Star (LRegex a)
 | LookAhead (LRegex a)
 | LookBehind (LRegex a)
 | NegLookAhead (LRegex a)
 | NegLookBehind (LRegex a)

try_upto :: (Prelude.Int -> Prelude.Bool) -> Prelude.Int -> Prelude.Bool
try_upto f n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f 0)
    (\n' -> (Prelude.||) (f n) (try_upto f n'))
    n

concat_aux :: ((([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool) ->
              ((([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool) ->
              (([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Int ->
              Prelude.Bool
concat_aux lang1 lang2 w start delta i =
  (Prelude.&&) (lang1 w start i)
    (lang2 w ((Prelude.+) start i) (sub delta i))

concat :: ((([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool) -> ((([])
          a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool) -> (([]) 
          a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool
concat lang1 lang2 w start delta =
  try_upto (concat_aux lang1 lang2 w start delta) delta

try_upto_1 :: (Prelude.Int -> Prelude.Bool) -> Prelude.Int -> Prelude.Bool
try_upto_1 f n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.False)
    (\n' -> (Prelude.||) (f n) (try_upto_1 f n'))
    n

concat_nonempty :: ((([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool)
                   -> ((([]) a1) -> Prelude.Int -> Prelude.Int ->
                   Prelude.Bool) -> (([]) a1) -> Prelude.Int -> Prelude.Int
                   -> Prelude.Bool
concat_nonempty lang1 lang2 w start delta =
  try_upto_1 (concat_aux lang1 lang2 w start delta) delta

star_aux :: Prelude.Int -> ((([]) a1) -> Prelude.Int -> Prelude.Int ->
            Prelude.Bool) -> (([]) a1) -> Prelude.Int -> Prelude.Int ->
            Prelude.Bool
star_aux x lang w start delta =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\x' -> concat_nonempty lang (star_aux x' lang) w start delta)
      x)
    delta

kleene_star :: ((([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool) ->
               (([]) a1) -> Prelude.Int -> Prelude.Int -> Prelude.Bool
kleene_star lang w start delta =
  star_aux delta lang w start delta

compute_regex :: (LRegex a1) -> (([]) a1) -> Prelude.Int -> Prelude.Int ->
                 Prelude.Bool
compute_regex r w start delta =
  case r of {
   Epsilon -> (Prelude.==) delta 0;
   CharClass p ->
    case (Prelude.==) delta (Prelude.succ 0) of {
     Prelude.True ->
      case nth_error w start of {
       Prelude.Just a -> p a;
       Prelude.Nothing -> Prelude.False};
     Prelude.False -> Prelude.False};
   Concat r1 r2 -> concat (compute_regex r1) (compute_regex r2) w start delta;
   Union r1 r2 ->
    (Prelude.||) (compute_regex r1 w start delta)
      (compute_regex r2 w start delta);
   Star r0 -> kleene_star (compute_regex r0) w start delta;
   LookAhead r0 ->
    (Prelude.&&) (compute_regex r0 w start (sub (length w) start))
      ((Prelude.==) delta 0);
   LookBehind r0 ->
    (Prelude.&&) (compute_regex r0 w 0 start) ((Prelude.==) delta 0);
   NegLookAhead r0 ->
    (Prelude.&&) ((Prelude.==) delta 0)
      (Prelude.not (compute_regex r0 w start (sub (length w) start)));
   NegLookBehind r0 ->
    (Prelude.&&) ((Prelude.==) delta 0)
      (Prelude.not (compute_regex r0 w 0 start))}

