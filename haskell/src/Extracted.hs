module Extracted where

import qualified Prelude

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

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

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

combine :: (([]) a1) -> (([]) a2) -> ([]) ((,) a1 a2)
combine l l' =
  case l of {
   ([]) -> ([]);
   (:) x tl ->
    case l' of {
     ([]) -> ([]);
     (:) y tl' -> (:) ((,) x y) (combine tl tl')}}

skipn :: Prelude.Int -> (([]) a1) -> ([]) a1
skipn n l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> l)
    (\n0 -> case l of {
             ([]) -> ([]);
             (:) _ l0 -> skipn n0 l0})
    n

seq :: Prelude.Int -> Prelude.Int -> ([]) Prelude.Int
seq start len =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\len0 -> (:) start (seq (Prelude.succ start) len0))
    len

repeat :: a1 -> Prelude.Int -> ([]) a1
repeat x n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\k -> (:) x (repeat x k))
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

zipWith :: (a1 -> a2 -> a3) -> (([]) a1) -> (([]) a2) -> ([]) a3
zipWith f xs ys =
  map (\pat -> case pat of {
                (,) x y -> f x y}) (combine xs ys)

transpose :: Prelude.Int -> (([]) (([]) a1)) -> ([]) (([]) a1)
transpose len tapes =
  case tapes of {
   ([]) -> repeat ([]) len;
   (:) t ts -> zipWith (\x x0 -> (:) x x0) t (transpose len ts)}

altr :: (Prelude.Maybe a1) -> (Prelude.Maybe a1) -> Prelude.Maybe a1
altr a b =
  case b of {
   Prelude.Just _ -> b;
   Prelude.Nothing -> a}

last_Some :: (([]) (Prelude.Maybe a1)) -> Prelude.Maybe a1
last_Some l =
  fold_right altr Prelude.Nothing l

opt_enum :: (([]) Prelude.Bool) -> ([]) (Prelude.Maybe Prelude.Int)
opt_enum lb =
  zipWith (\b i ->
    case b of {
     Prelude.True -> Prelude.Just i;
     Prelude.False -> Prelude.Nothing}) lb (seq 0 (length lb))

find_largest_true :: (([]) Prelude.Bool) -> Prelude.Maybe Prelude.Int
find_largest_true lb =
  last_Some (opt_enum lb)

type Valuation = ([]) Prelude.Bool

type Ostring a = (,) (([]) a) (([]) Valuation)

oskipn :: Prelude.Int -> (Ostring a1) -> Ostring a1
oskipn n s =
  (,) (skipn n (fst s)) (skipn (Prelude.min n (length (fst s))) (snd s))

orev :: (Ostring a1) -> Ostring a1
orev s =
  (,) (Prelude.reverse (fst s)) (Prelude.reverse (snd s))

data ORegex a =
   OEpsilon
 | OCharClass (a -> Prelude.Bool)
 | OConcat (ORegex a) (ORegex a)
 | OUnion (ORegex a) (ORegex a)
 | OStar (ORegex a)
 | OQueryPos Prelude.Int
 | OQueryNeg Prelude.Int

oWildCard :: ORegex a1
oWildCard =
  OStar (OCharClass (\_ -> Prelude.True))

rPass :: (ORegex a1) -> ORegex a1
rPass or =
  OConcat oWildCard or

oreverse :: (ORegex a1) -> ORegex a1
oreverse r =
  case r of {
   OConcat r1 r2 -> OConcat (oreverse r2) (oreverse r1);
   OUnion r1 r2 -> OUnion (oreverse r1) (oreverse r2);
   OStar r0 -> OStar (oreverse r0);
   x -> x}

type Tape = ([]) Prelude.Bool

data CMRegex a =
   MkCMRegex Prelude.Bool Prelude.Bool (CMRe a)
data CMRe a =
   CMEpsilon
 | CMCharClass (a -> Prelude.Bool)
 | CMQueryPos Prelude.Int
 | CMQueryNeg Prelude.Int
 | CMConcat (CMRegex a) (CMRegex a)
 | CMUnion (CMRegex a) (CMRegex a)
 | CMStar (CMRegex a)

cNullable :: (CMRegex a1) -> Prelude.Bool
cNullable r =
  case r of {
   MkCMRegex b _ _ -> b}

cFinal :: (CMRegex a1) -> Prelude.Bool
cFinal r =
  case r of {
   MkCMRegex _ b _ -> b}

cRe :: (CMRegex a1) -> CMRe a1
cRe r =
  case r of {
   MkCMRegex _ _ re -> re}

mkEpsilon :: CMRegex a1
mkEpsilon =
  MkCMRegex Prelude.True Prelude.False CMEpsilon

mkCharClass :: Prelude.Bool -> (a1 -> Prelude.Bool) -> CMRegex a1
mkCharClass mark f =
  MkCMRegex Prelude.False mark (CMCharClass f)

mkQueryPos :: Prelude.Bool -> Prelude.Int -> CMRegex a1
mkQueryPos b n =
  MkCMRegex b Prelude.False (CMQueryPos n)

mkQueryNeg :: Prelude.Bool -> Prelude.Int -> CMRegex a1
mkQueryNeg b n =
  MkCMRegex b Prelude.False (CMQueryNeg n)

mkConcat :: (CMRegex a1) -> (CMRegex a1) -> CMRegex a1
mkConcat r1 r2 =
  MkCMRegex ((Prelude.&&) (cNullable r1) (cNullable r2))
    ((Prelude.||) ((Prelude.&&) (cFinal r1) (cNullable r2)) (cFinal r2))
    (CMConcat r1 r2)

mkUnion :: (CMRegex a1) -> (CMRegex a1) -> CMRegex a1
mkUnion r1 r2 =
  MkCMRegex ((Prelude.||) (cNullable r1) (cNullable r2))
    ((Prelude.||) (cFinal r1) (cFinal r2)) (CMUnion r1 r2)

mkStar :: (CMRegex a1) -> CMRegex a1
mkStar r =
  MkCMRegex Prelude.True (cFinal r) (CMStar r)

syncVal :: Valuation -> (CMRegex a1) -> CMRegex a1
syncVal v r =
  case cRe r of {
   CMEpsilon -> mkEpsilon;
   CMCharClass f -> mkCharClass (cFinal r) f;
   CMQueryPos n ->
    mkQueryPos
      (case nth_error v n of {
        Prelude.Just b -> b;
        Prelude.Nothing -> Prelude.False}) n;
   CMQueryNeg n ->
    mkQueryNeg
      (case nth_error v n of {
        Prelude.Just b ->
         case b of {
          Prelude.True -> Prelude.False;
          Prelude.False -> Prelude.True};
        Prelude.Nothing -> Prelude.False}) n;
   CMConcat r1 r2 -> mkConcat (syncVal v r1) (syncVal v r2);
   CMUnion r1 r2 -> mkUnion (syncVal v r1) (syncVal v r2);
   CMStar r1 -> mkStar (syncVal v r1)}

cRead :: a1 -> (CMRegex a1) -> CMRegex a1
cRead a r =
  case cRe r of {
   CMCharClass f -> mkCharClass ((Prelude.&&) (cFinal r) (f a)) f;
   CMConcat r1 r2 -> mkConcat (cRead a r1) (cRead a r2);
   CMUnion r1 r2 -> mkUnion (cRead a r1) (cRead a r2);
   CMStar r1 -> mkStar (cRead a r1);
   _ -> r}

cFollow :: Prelude.Bool -> (CMRegex a1) -> CMRegex a1
cFollow b r =
  case cRe r of {
   CMEpsilon -> mkEpsilon;
   CMCharClass f -> mkCharClass b f;
   CMConcat r1 r2 ->
    let {b1 = (Prelude.||) (cFinal r1) ((Prelude.&&) b (cNullable r1))} in
    mkConcat (cFollow b r1) (cFollow b1 r2);
   CMUnion r1 r2 -> mkUnion (cFollow b r1) (cFollow b r2);
   CMStar r1 -> mkStar (cFollow ((Prelude.||) b (cFinal r1)) r1);
   _ -> r}

toCMarked :: (ORegex a1) -> CMRegex a1
toCMarked or =
  case or of {
   OEpsilon -> mkEpsilon;
   OCharClass f -> mkCharClass Prelude.False f;
   OConcat or1 or2 -> mkConcat (toCMarked or1) (toCMarked or2);
   OUnion or1 or2 -> mkUnion (toCMarked or1) (toCMarked or2);
   OStar or1 -> mkStar (toCMarked or1);
   OQueryPos n -> mkQueryPos Prelude.False n;
   OQueryNeg n -> mkQueryNeg Prelude.False n}

cScanMatchAux :: (CMRegex a1) -> (([]) a1) -> (([]) Valuation) -> ([])
                 Prelude.Bool
cScanMatchAux cmr w o =
  let {b = cFinal cmr} in
  case w of {
   ([]) -> (:) b ([]);
   (:) a0 w' ->
    case o of {
     ([]) -> (:) b ([]);
     (:) v1 o' ->
      let {cmrNew = cFollow Prelude.False cmr} in
      let {cmrNew' = cRead a0 cmrNew} in
      let {cmrNew'' = syncVal v1 cmrNew'} in
      (:) b (cScanMatchAux cmrNew'' w' o')}}

cScanMatch :: (ORegex a1) -> (Ostring a1) -> ([]) Prelude.Bool
cScanMatch or os =
  let {cmr = toCMarked or} in
  case os of {
   (,) l l0 ->
    case l of {
     ([]) ->
      case l0 of {
       ([]) -> ([]);
       (:) o0 l1 ->
        case l1 of {
         ([]) -> (:) (cNullable (syncVal o0 cmr)) ([]);
         (:) _ _ -> ([])}};
     (:) a0 w' ->
      case l0 of {
       ([]) -> ([]);
       (:) o0 l1 ->
        case l1 of {
         ([]) -> ([]);
         (:) o1 o' ->
          let {b0 = cNullable (syncVal o0 cmr)} in
          let {cmr0 = cFollow Prelude.True (syncVal o0 cmr)} in
          let {cmr0' = cRead a0 cmr0} in
          let {cmr0'' = syncVal o1 cmr0'} in
          (:) b0 (cScanMatchAux cmr0'' w' o')}}}}

absEvalAux :: ((ORegex a1) -> (Ostring a1) -> Tape) -> (([]) a1) -> (([]) 
              a1) -> Prelude.Int -> (LRegex a1) -> Prelude.Int -> (([]) 
              Tape) -> (,) ((,) (ORegex a1) Prelude.Int) (([]) Tape)
absEvalAux scanMatch0 w wrev len r i ts =
  case r of {
   Epsilon -> (,) ((,) OEpsilon 0) ts;
   CharClass p -> (,) ((,) (OCharClass p) 0) ts;
   Concat r1 r2 ->
    case absEvalAux scanMatch0 w wrev len r1 i ts of {
     (,) p ts' ->
      case p of {
       (,) o1 n1 ->
        case absEvalAux scanMatch0 w wrev len r2 ((Prelude.+) i n1) ts' of {
         (,) p0 ts'' ->
          case p0 of {
           (,) o2 n2 -> (,) ((,) (OConcat o1 o2) ((Prelude.+) n1 n2)) ts''}}}};
   Union r1 r2 ->
    case absEvalAux scanMatch0 w wrev len r1 i ts of {
     (,) p ts' ->
      case p of {
       (,) o1 n1 ->
        case absEvalAux scanMatch0 w wrev len r2 ((Prelude.+) i n1) ts' of {
         (,) p0 ts'' ->
          case p0 of {
           (,) o2 n2 -> (,) ((,) (OUnion o1 o2) ((Prelude.+) n1 n2)) ts''}}}};
   Star r0 ->
    case absEvalAux scanMatch0 w wrev len r0 i ts of {
     (,) p ts' -> case p of {
                   (,) o n -> (,) ((,) (OStar o) n) ts'}};
   LookAhead r0 ->
    case absEvalAux scanMatch0 w wrev len r0 0 ([]) of {
     (,) p ts_inner ->
      case p of {
       (,) o _ ->
        let {vs = transpose len (Prelude.reverse ts_inner)} in
        let {
         newtape = Prelude.reverse
                     (scanMatch0 (oreverse o) ((,) wrev
                       (Prelude.reverse vs)))}
        in
        (,) ((,) (OQueryPos i) (Prelude.succ 0)) ((:) newtape ts)}};
   LookBehind r0 ->
    case absEvalAux scanMatch0 w wrev len r0 0 ([]) of {
     (,) p ts_inner ->
      case p of {
       (,) o _ ->
        let {vs = transpose len (Prelude.reverse ts_inner)} in
        let {newtape = scanMatch0 o ((,) w vs)} in
        (,) ((,) (OQueryPos i) (Prelude.succ 0)) ((:) newtape ts)}};
   NegLookAhead r0 ->
    case absEvalAux scanMatch0 w wrev len r0 0 ([]) of {
     (,) p ts_inner ->
      case p of {
       (,) o _ ->
        let {vs = transpose len (Prelude.reverse ts_inner)} in
        let {
         newtape = Prelude.reverse
                     (scanMatch0 (oreverse o) ((,) wrev
                       (Prelude.reverse vs)))}
        in
        (,) ((,) (OQueryNeg i) (Prelude.succ 0)) ((:) newtape ts)}};
   NegLookBehind r0 ->
    case absEvalAux scanMatch0 w wrev len r0 0 ([]) of {
     (,) p ts_inner ->
      case p of {
       (,) o _ ->
        let {vs = transpose len (Prelude.reverse ts_inner)} in
        let {newtape = scanMatch0 o ((,) w vs)} in
        (,) ((,) (OQueryNeg i) (Prelude.succ 0)) ((:) newtape ts)}}}

absEval :: ((ORegex a1) -> (Ostring a1) -> Tape) -> (([]) a1) -> (LRegex 
           a1) -> (,) (ORegex a1) (([]) Valuation)
absEval scanMatch0 w r =
  let {wrev = Prelude.reverse w} in
  let {len = length w} in
  case absEvalAux scanMatch0 w wrev ((Prelude.+) len (Prelude.succ 0)) r 0
         ([]) of {
   (,) p vs ->
    case p of {
     (,) o _ -> (,) o
      (transpose ((Prelude.+) len (Prelude.succ 0)) (Prelude.reverse vs))}}

scanMatchWith :: ((ORegex a1) -> (Ostring a1) -> Tape) -> (([]) a1) ->
                 (LRegex a1) -> Tape
scanMatchWith scanMatchONFA w r =
  case absEval scanMatchONFA w r of {
   (,) o vs -> scanMatchONFA o ((,) w vs)}

scanMatch :: (LRegex a1) -> (([]) a1) -> Tape
scanMatch r w =
  scanMatchWith cScanMatch w r

llmatch :: (LRegex a1) -> (([]) a1) -> Prelude.Maybe
           ((,) Prelude.Int Prelude.Int)
llmatch r w =
  case absEval cScanMatch w r of {
   (,) or vs ->
    let {bw_tape = cScanMatch (rPass (oreverse or)) (orev ((,) w vs))} in
    let {lendO = find_largest_true bw_tape} in
    case lendO of {
     Prelude.Just lend' ->
      let {lend = sub (length w) lend'} in
      let {fw_tape = cScanMatch or (oskipn lend ((,) w vs))} in
      let {d = find_largest_true fw_tape} in
      case d of {
       Prelude.Just d0 -> Prelude.Just ((,) lend d0);
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

