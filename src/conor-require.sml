(* A tool for organising the generation and storage of lemmas used in and *)
(* manufactured by tactics, both during proofs and ancillary to           *)
(* definitions.                                                           *)

signature CONORREQUIRE =
sig
  exception RequireFailure
  val Memo                : string list -> ((cnstr * cnstr) * bool)
  val RequireFail         : string list -> ((cnstr * cnstr) * bool)
  val AddRequireDemon     : (string list -> ((cnstr * cnstr) * bool)) -> unit
  val Require             : string list -> (cnstr * cnstr)
  val ConfigMemo          : (string list * string) -> unit
  val RequireTac          : string list -> unit
  val tagName             : string list -> string
(* *)
  val requireDemons : (string list -> ((cnstr * cnstr) * bool)) list ref
(* *)
end

(* Let a `demon' be a function string list -> ((cnstr * cnstr) * bool)     *)
(* which either succeeds or raises RequireFailure. Demons search for   *)
(* the value corresponding to the tag, which they return if they find  *)
(* it, aLong with a boolean value indicating whether the given result  *)
(* should be memoised.                                                 *)

(* Memo is intended to be a demon which checks if the given tag has    *)
(* already been given a value, in which case, that is the value        *)
(* returned.                                                           *)

(* RequireFail is the demon which always fails.                        *)

(* AddRequireDemon adds a demon to a growing stack of demons, kept     *)
(* privately.                                                          *)

(* Require is first tries Memo. If Memo fails, then the                *)
(* stacked demons are tried in turn until one succeeds. If this is ok  *)
(* and the memoisation flag is true, then Require attempts to add the  *)
(* computed definition to the context so that Memo will find it next   *)
(* time, but even if definition is not possible, Require will still    *)
(* return a typed term matching the tag if a demon makes one.          *)


(***********************************************************************
November 1999: Conor's `temporary' fix to make the Require mechanism
go via the Quartermaster
***********************************************************************)

functor ConorRequire ( structure Concrete : CONCRETE
                       structure Quartermaster : QUARTERMASTER
                       sharing type Quartermaster.cnstr_c = Concrete.cnstr_c
                     ) : CONORREQUIRE =
struct
  local
    open Concrete
    open Quartermaster
  in
    exception RequireFailure
    fun RequireFail _ = raise RequireFailure
    fun Memo rtag = 
        let val made = Make (SLtoCL rtag)
        in (fEval made,false)
        end
        handle quartermaster => raise RequireFailure
    fun Require rtag = 
        let val made = Make (SLtoCL rtag)
        in fEval made
        end
        handle quartermaster => raise RequireFailure
    fun AddRequireDemon reqd =
        let fun quard ccl =
                case CLtoSLo ccl
                  of NONE => raise quartermaster
                   | SOME rtag =>
                     let val ((v,t),b) = reqd rtag
                     in (unEval v,b)
                     end
                     handle RequireFailure => raise quartermaster
        in  Register quard
        end
    fun ConfigMemo (ss,s) = Label ss s
    fun RequireTac ss = Generate ss (Let,VBot,(UnFroz,Global),[],[],Prop_c)
    fun tagName [] = ""
      | tagName [s] = s
      | tagName (h::t) = h^"_"^(tagName t)
(* atavistic *)
    val requireDemons = ref ([]:(string list -> ((cnstr * cnstr) * bool)) list)
(* as is the whole thing, I guess *)
  end
end








(*****************************************************************







(* In here, we abstract out the services we need from the rest of LEGO *)
(* except for the things which never get packaged up, like cnstr...    *)
(* Also, the utility functions whose names I can never remember...     *)

signature CONORREQUIRENEEDS =
sig
  val IntToString : int -> string
  exception thatWasABadTerm
  exception iCantDefineThingsRightNow of cnstr * cnstr
  val tagName : string list -> string
  val TryToDefine : string list -> (cnstr * cnstr) -> (cnstr * cnstr)
              (*        `tag'     `term'    `type'    `checked pair' *)
              (* This checks that the term is well-typed, then tries to    *)
              (* bind the given name to the term in the context. If this   *)
              (* name is already taken, another is chosen and the alias    *)
              (* registered. If definition isn't possible right now, the   *)
              (* relevant exception is raised with the typed term in the   *)
              (* packet, indicating that the term can still be used in a   *)
              (* proof...                                                  *)
  val MemoMark : (string list * string) -> unit
  val TypeCheck : cnstr -> (cnstr * cnstr)
  type nameSpace
  datatype nsEntry = nsBind of (string * (cnstr * cnstr))
                   | nsMemo of (string * string)
  exception nsUnderflow
  val GetNameSpace : unit -> nameSpace
  val NsSplit : nameSpace -> (nsEntry * nameSpace)
  (***************************************************************)
  (* stuff below this box is stuff we want to get rid of         *)
  (***************************************************************)
end

functor ConorRequire ( structure ConorRequireNeeds : CONORREQUIRENEEDS
                     ) : CONORREQUIRE =
struct
  exception RequireFailure
  local
    open ConorRequireNeeds

    (***************************************************************)
    (* some Require demons we need for compatibility reasons       *)
    (* but we should get rid of in due course...                   *)
    (***************************************************************)

    (***************************************************************)
(*
    val requireDemons = ref ([]:(string list -> ((cnstr * cnstr) * bool)) list)
*)
    fun memoise tag stuff =
        TryToDefine tag stuff
        handle iCantDefineThingsRightNow tmty => tmty

  in
(* *)
    val requireDemons = ref ([]:(string list -> ((cnstr * cnstr) * bool)) list)
(* *)
    fun RequireFail _ = raise RequireFailure
    fun Memo tag =
      let val name = tagName tag
          fun find want (nsBind (got,result),rest) =
              if got=want then (result,false) else find want (NsSplit rest)
            | find want (nsMemo (atag,aka),rest) =
              if atag=name
                then find aka (NsSplit rest)
              else find want (NsSplit rest)
      in  find "]" (NsSplit (GetNameSpace ()))
          handle nsUnderflow => raise RequireFailure
      end
    fun AddRequireDemon demon =
      ( requireDemons := demon :: (!requireDemons) )
    fun Require tag =
        let fun tryStack [] = raise RequireFailure
              | tryStack (h::t) = h tag
                                  handle RequireFailure => tryStack t
            val (result,memo) = tryStack (Memo::(!requireDemons))
        in  if memo then memoise tag result else result
        end
    fun ConfigMemo (x as (tag,id)) = ( (MemoMark x);
                                       (message (id^" memoised\n")) )
    fun RequireTac tag = ( (Require tag); ())
                         handle RequireFailure =>
                         failwith "Require failed\n"
    val tagName = tagName
  end
end

(* Down here go the gory details *)

functor ConorRequireNeeds ( structure NameSpace : NAMESPACE
                            structure Concrete : CONCRETE
                          ) : CONORREQUIRENEEDS =
struct
  local
    open NameSpace
    open Concrete
  in
    val IntToString = string_of_num (* so that's what it's called! *)
                                    (* of course, if this was mosml, I'd
                                       have had to write it myself...    *)
    exception thatWasABadTerm
    exception iCantDefineThingsRightNow of cnstr * cnstr
    fun tagName [] = ""
      | tagName [s] = s
      | tagName (h::t) = h^"_"^(tagName t)
    fun MemoMark (tag,name) = addConfig ("Memo",tagName tag,name,"")
    fun TryToDefine tag (tm,ty) =
      let val term_c = Cast_c (unEval tm,unEval ty)
              handle _ => raise thatWasABadTerm
          val nicePair = fEval term_c
              handle _ => raise thatWasABadTerm
          val choice = tagName tag
          val realName = mkNameGbl choice
      in  if (not (activeProofState()))
          then ( (extendCxtGbl Bnd (Let,Def)
                   (UnFroz,Global) [] realName nicePair);
                 (MemoMark (tag,realName));
                 (print "Adding ");
                 (map (fn s => (print (" "^s))) tag);
                 (print ("  with name  "^realName^"\n"));
                 (fEval (Ref_c realName)) )
          else raise iCantDefineThingsRightNow nicePair
          handle _ => raise iCantDefineThingsRightNow nicePair
      end
    fun TypeCheck term = (term,(!toc) term)
    type nameSpace = binding list
    datatype nsEntry = nsBind of (string * (cnstr * cnstr))
                     | nsMemo of (string * string)
    exception nsUnderflow
    val GetNameSpace = getNamespace
    fun NsSplit [] = raise nsUnderflow
      | NsSplit ((ref (Bd {kind=Bnd,bd=(_,name,_,_),...}))::rest) =
        ( (nsBind (name,fEval (Ref_c name)),rest)
          handle _ => NsSplit rest  )
      | NsSplit ((ref (Bd {kind=Config(i,a,b,c),...}))::rest) =
        if i="Memo" then (nsMemo (a,b),rest)
        else NsSplit rest
      | NsSplit (_::rest) = NsSplit rest
  end
end

(*
structure ConorRequireNeeds = ConorRequireNeeds (
        structure NameSpace = Namespace
        structure Concrete = Concrete)

structure ConorRequire = ConorRequire (
        structure ConorRequireNeeds = ConorRequireNeeds)
*)

*********************************************************)

signature CONORREADSTRING =
sig
  val readString          : string -> (cnstr * cnstr)
  val theBox              : (cnstr * cnstr) ref
end

functor ConorReadString ( structure Modules : MODULES ) : CONORREADSTRING =
struct
local
   open Modules
in
    val theBox = ref (Bot,Bot)
    fun readString s =
        (((!legoStringParser) ("BoxTerm "^s));(!theBox))
end
end

