fun opStrip ("o"::"p"::s') = s'
  | opStrip s = s

val spesh = [".","*","+","?","[","]","^","$","\\"]

fun escapeSpesh [] = []
  | escapeSpesh (x::xs) = if member x spesh then ("\\"::x::escapeSpesh xs)
                          else x::(escapeSpesh xs)

val emacsName = implode o escapeSpesh o opStrip o explode

val doingEmacs = ref true

fun doEmacs s = if !doingEmacs then print ("EMACS%%%"^s^"%%%\n") else ()

fun emacsAdd [] col = "nil"
  | emacsAdd (x::xs) col =
    let fun choice s [] = s
          | choice s (x::xs) = choice (s^"\\\\|"^(emacsName x)) xs
        val namestring = choice (emacsName x) xs
        val cmdstring = "(lego-add-var \""^namestring^"\" (quote "^col^")) "
    in  cmdstring
    end

local
  fun ep2 s [] = s^")"
    | ep2 s (x::xs) = ep2 (s^" "^x) xs
in
fun emacsProg ss = ep2 "(progn" ss
end

