(************************************************************************)
(**********                                                    **********)
(**********          datatypes for Oleg                        **********)
(**********                                                    **********)
(************************************************************************)

datatype Back = Dom | Ran

datatype Owner = Core | Dev

datatype OlegState = Component of {back  : Back,
                                   ctxt  : OlegState ref,
                                   name  : string * int,
                                   bind  : binding,
                                   dom   : OlegState ref,
                                   ran   : OlegState ref,
                                   owner : Owner}
                   | LegoContext of OlegState ref
                   | Tip of OlegState ref * cnstr
                   | Top of OlegState ref
                   | Cloud of {bef:OlegState ref,
                               fst:OlegState ref,
                               lst:OlegState ref,
                               aft:OlegState ref}
                   | Bogus

(*********
val top = ref Bogus
val lcxt = ref (LegoContext top)
val _ = top := Top lcxt
************)

local

fun brack f b s = f^s^b

fun mult s 0 = ""
  | mult s n = s^(mult s (n-1))

fun indent i s = (mult "! "i)^s

fun bstr Pi = "All  "
  | bstr Lda = "Lda  "
  | bstr Let = "Let  "
  | bstr Sig = "Sig  "
  | bstr Hole = "Hole "
  | bstr _ = "Hmmm "

fun vstr Hole Def = " :"
  | vstr _ Vis = " :"
  | vstr _ Hid = " |"
  | vstr _ Def = " ="
  | vstr _ Guess = " ?="
  | vstr _ VBot = " ?"

fun bheader bf bb bd (s,i) =
    let val ((b,v),_,_,_) = ref_bd bd
    in bf^(bstr b)^s^(string_of_num i)^bb^(vstr b v)
    end

in

fun OlegDisplay spesh ind state =
    let val (bf,bb) = assoc state spesh handle Assoc => (" "," ")
    in  case !state
          of LegoContext s => ((print "**LEGO**\n");
                               (OlegDisplay spesh 0 s))
           | Component {bind=bd,dom=d,ran=r,name=n,...} =>
             (case !d
                of Tip (_,t) => ((print (bheader bf bb bd n));
                                 (print " ");
                                 (OlegDisplay spesh 0 d);
                                 (OlegDisplay spesh ind r))
                 | _ => ((print (bheader bf bb bd n));(print "\n");
                         (OlegDisplay spesh (ind+1) d);
                         (OlegDisplay spesh ind r)))
           | Tip (_,t) => ((print (indent ind ""));
                           (print bf);(legoprint t);(print bb);
                           (print "\n"))
           | Top _ => print "**OLEG**\n"
           | Cloud r => ((print (indent ind "Cloud\n"));
                         (OlegDisplay spesh ind (#aft r)))
           | Bogus => ()
    end
end

fun ODisp state = OlegDisplay [] 0 state