fun mkList f start finish =
    let fun mk i = if i>finish then [] else (f i)::(mk (i+1))
    in  mk start
    end

fun nodup x l = if member x l then l else x::l

fun union x y = foldr nodup y x

fun on X [] = X
  | on X (h::t) = on (h X) t

infix **

fun (f**g) (a,b) = (f a,g b)

fun iota x = x

fun cons h t = h::t

fun folder glue blat l X = foldr (fn h => glue (blat h) handle _ => iota) X l

fun filter $ =
    foldr (fn h => if $h then ((cons h)**iota) else (iota**(cons h))) ([],[])

open ConorReadString

fun ?s = #1 (readString s)
fun %s = #2 (readString s)

fun depth (Bind (_,_,_,r)) = 1+(depth r)
  | depth _ = 0

fun shop f F X = case F X
                   of UMod => UMod
                    | Mod x => Mod (f x)

fun joint [] l = false
  | joint (h::t) l = (member h l) orelse joint t l

fun pair a b = (a,b)

fun const a b = a

exception scarySplice

fun splice mang l bum =
    let fun spl1 (l as ((h::t)::_)) =
            let val cdrs = (map tl l) handle _ => raise scarySplice
                val spliceTail = spl1 cdrs
                fun spl2 [] = spliceTail
                  | spl2 ((h::_)::t) = (mang h)::(spl2 t)
                  | spl2 _ = raise scarySplice
            in  spl2 l
            end
          | spl1 ([]::t) =
            let fun chk [] = bum
              | chk ([]::t) = chk t
              | chk _ = raise scarySplice
            in  chk t
            end
          | spl1 [] = bum
    in  spl1 l
    end

fun zAssoc ll vv l =
    let fun za2 (lh::lt) (vh::vt) = if lh=l then vh else za2 lt vt
          | za2 _ _ = raise Assoc
    in  za2 ll vv
    end
