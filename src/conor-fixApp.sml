(* This bit of code is a funny kind of fEval designed to repair
   problems with visibilities in applications introduced by a feature of
   the reduction engine. *)

local

fun isOneAVar [] = false
  | isOneAVar ((Var _)::_) = true
  | isOneAVar (_::t) = isOneAVar t

fun mangle2 (App_c (NoShow,f,a)) = App_c (ShowForce,mangle2 f,a)
  | mangle2 (App_c (pv,f,a)) = App_c (pv,mangle2 f,a)
  | mangle2 x = x

fun mangle ((Var _)::t) (App_c (NoShow,f,a)) = App_c (ShowForce,mangle2 f,a)
  | mangle (_::t) (App_c (pv,f,a)) = App_c (pv,mangle t f,a)
  | mangle _ x = x

fun fixApp_ Cxt type_of_var mkVar V_c =
  let

    (* The following is ripped off Machine.Apply, which is the bit that does
       argument synthesis and application typechecking. Here we should never
       have to infer any args, but we want to make sure that the print
       visibilities of an arg corresponds to the bind visibilities of
       the function. *)
    
    exception Bungle
    fun fixMachApply sbst pv (VTf as (Vf,Tf)) (VTa as (Va,Ta)) =
        let val Tf = whnf (sub sbst Tf)
            fun backEnd pv (dom,rng) (Va,Ta) =
                case par_unif sbst Ta dom
                  of SOME s => ((MkApp((Vf,[Va]),[pv]),
                                 coerceGe (subst1 Va rng)),s)
                   | NONE => raise Bungle
        in  case (pv,Tf,VTa)
              of (* fix minor clerical errors *)
                 (ShowNorm,Bind((Pi,Hid),nam,dom,rng),_) =>
                   backEnd ShowForce (dom,rng) VTa
               | (ShowForce,Bind((Pi,Vis),nam,dom,rng),_) =>
                   backEnd ShowNorm (dom,rng) VTa
               | (NoShow,Bind((Pi,Vis),nam,dom,rng),_) =>
                   backEnd ShowNorm (dom,rng) VTa
                 (* to make sure we really can infer the hidden argument
                    we omit it now and check it later *)
               | (NoShow,Bind((Pi,Hid),nam,dom,rng),_)  =>
                   backEnd NoShow (dom,rng) (mkVar dom,Ta)
                 (* otherwise, everything's normal *)
               | (ShowNorm,Bind((Pi,Vis),nam,dom,rng),_) =>
                   backEnd ShowNorm (dom,rng) VTa
               | (ShowForce,Bind((Pi,Hid),nam,dom,rng),_) =>
                   backEnd ShowForce (dom,rng) VTa
               | _  => raise Error.error (Error.APPLNNFUN,NONE,[Vf, dnf Tf])
        end    

    fun fixbinder (b,v,frz_par_flg,_,nam,d) inner_op cxt sbst =
      let 
	val (VT,sbst) = fixEval cxt sbst d
	val cxt = Namespace.extendCxt Bnd (b,v) frz_par_flg [] nam VT cxt
	val (VTr,sbst) = inner_op cxt sbst
	val (VT,_,_) = Namespace.dischCxt VTr cxt
      in  (VT,sbst)
      end
    and fixEv_locs locs inner_op cxt sbst =
      case locs
	of (b,v,frz_par_flg,deps,n::ns,d)
	  => fixbinder (b,v,frz_par_flg,deps,n,d)
	    (fixEv_locs (b,v,frz_par_flg,deps,ns,d) inner_op)
	    cxt sbst
	| (_,_,_,_,[],_)    => inner_op cxt sbst 
    and fixEvLocs locs inner_op cxt sbst =
      case locs
	of bnd::bnds => fixEv_locs bnd (fixEvLocs bnds inner_op) cxt sbst
	 | []        => inner_op cxt sbst

    and fixEval cxt sbst c =
      let val (VT,sbst) = fixeval cxt sbst c
      in (sub_pr sbst VT,sbst) end
    and fixCval c cxt sbst = fixEval cxt sbst c

    and fixEvalFun cxt sbst (App_c(pv,fnn,arg)) =
      let fun fixEval_arg cxt sbst =
	      fn NewVar_c => ((Bot,Bot),sbst)   (* just a marker for Apply *)
	       | x        => fixEval cxt sbst x
          val (VTfun,sbst) = fixEvalFun cxt sbst fnn
	  val (VTarg,sbst) = fixEval_arg cxt sbst arg
	  val (VT,sbst) = fixMachApply sbst pv VTfun VTarg
      in (sub_pr sbst VT,sbst) end
      | fixEvalFun cxt sbst c = fixEval cxt sbst c

    and fixeval cxt sbst c =
      let
	val _ = if (!eval_debug) then message("** eval_deb: "^prt_concrete c)
		else ()
	fun fixEval_arg cxt sbst =
	  fn NewVar_c => ((Bot,Bot),sbst)   (* just a marker for Apply *)
	   | x        => fixEval cxt sbst x
      in case c of
	Prop_c => (Machine.ConsiderProp(),sbst)
      | Theory_c => (Machine.ConsiderTheory(),sbst)
      | Type_c s => (Machine.ConsiderType s,sbst)
      | TypeAbs_c(n) =>
	     if (n>=0) then (Machine.ConsiderTypen n,sbst)
	     else failwith((string_of_num n)^" not a valid Type level")
      | Ref_c(nam) => (Consider nam cxt,sbst)
      | Bind_c(bnd,r) => fixEv_locs bnd (fixCval r) cxt sbst


      | App_c(pv,fnn,arg) =>
	 (let val (VTfun,sbst) = fixEvalFun cxt sbst fnn
	      val (VTarg,sbst) = fixEval_arg cxt sbst arg
	      val old as ((V,T),sbst) = fixMachApply sbst pv VTfun VTarg
          in case V
               of (App ((f,args),vis)) =>
                  if isOneAVar args
                  then fixEvalFun cxt sbst (mangle args c)
                  else old
                | _ => old
	  end
          handle Bungle => fixEvalFun cxt sbst (mangle2 c))
          
      | Tuple_c(cs,t) =>
	  let val ((T,_),sbst) = if t = Bot_c then ((Bot,Bot),sbst)
				 else fixEval cxt sbst t
	      fun ev c (vts,sbst) = let val (vt,sbst) = fixEval cxt sbst c
				    in  (vt::vts,sbst)
				    end
	      val (vts,sbst) = foldr ev ([],sbst) cs
	  in  Machine.tuplize sbst T vts
	  end
      | Proj_c(p,c) =>
	  (case (fixEval cxt sbst c,p)
	     of (((V,_),sbst),Labl l) => (TheoryProject(V,l),sbst)
	      | ((VT,sbst),_) => ((Machine.Projection p VT),sbst))
      | Case_c(v,branches) =>
	  (case fixEval cxt sbst v of
	     ((V,T),sbst) => ((Case(V,fixEvCase T branches cxt),T),sbst))
      | RedTyp_c(i,c)  => (case fixEval cxt sbst c of (****  temporary  *****)
			     ((v,t),sbst) => ((RedTyp(i,v),UMnorm t),sbst))
      | Cast_c(c,t)    => fixtypecheck cxt sbst c t
      | wCast_c(c,t)   => fixtypchk cxt sbst c t
      | Ctxt_c(locs,c) => fixEvLocs locs (fixCval c) cxt sbst
      | Red_c(red)     => fixEvRed red cxt
      | Var_c(n)       => ((Machine.ConsiderVar (n,Bot) (type_of_var n)),sbst)
      | NewVar_c       => failwith"new scheme vars not allowed here"
      | Bot_c          => bug"fEval_:Bot_c"
      | Normal_c(c)    => (case fixEval cxt sbst c of
			     ((v,t),sbst) => ((UMnorm v,UMnorm t),sbst))
      | Hnf_c(n,c)     => (case fixEval cxt sbst c of
			     ((v,t),sbst) => ((UMwhnf v,UMwhnf t),sbst))
      | Dnf_c(c)       => (case fixEval cxt sbst c of
			     ((v,t),sbst) => ((UMdnf v,UMdnf t),sbst))
      | TypeOf_c(c)    => (case fixEval cxt sbst c of
			     ((v,t),sbst) => ((t,type_of_constr t),sbst))
      | Gen_c(c,back)  => (case fixEval cxt sbst c of
			     (vt,sbst) => (Namespace.lclGen vt back,sbst))
      end
	 
    and fixchk_unresolved (VT as (V,T)) =
      if (semi_pure V) andalso (semi_pure T)
	then VT
      else (prnt_vt_expand V T; failwith "unresolved metavars")
    and fixfEv V_c cxt sbst = let val (VT,sbst) = fixEval cxt sbst V_c
			   in ((fixchk_unresolved VT),sbst) end
    and fixtypecheck cxt sbst pr cnj =  (* concrete conjecture *)
      let val ((Vcnj,_),sbst) = fixfEv cnj cxt sbst
      in  fixtypchk cxt sbst pr Vcnj
      end
    and fixtypchk cxt sbst pr cnj =     (* abstract conjecture *)
      case pr
	of NewVar_c => ((mkVar cnj,cnj),sbst)
	 | _        =>
	     let
	       val ((V,T),sbst) = fixfEv pr cxt sbst
	       val _ = if not(!eval_debug) then ()
		       else (message"**ev_deb: typchk ";
			     hold_T:= T; legoprint T;
			     hold_cnj:= cnj; legoprint cnj)
	     in case par_unif sbst T cnj
		  of SOME(s) => ((V,cnj),s)
		   | NONE => (message"typechecking error.."; legoprint V;
			      message"has type.."; legoprint T;
			      message"which doesn't convert with..";
			      legoprint cnj;
			      failwith "term doesn't have purported type")
	     end
    and fixchkPr lcl cxt sbst (lhs,rhs) =
      let
	val lclCxt = first_n lcl cxt
	val ((vlhs,tlhs),_) = fixEval cxt sbst lhs
	val ((vrhs,trhs),_) = fixEval cxt sbst rhs
	val _ = if (UMtype_match tlhs trhs) then ()
		else (message"reduction LHS has type ";legoprint tlhs;
		      message"reduction RHS has type ";legoprint trhs;
		      failwith"LHS and RHS types don't convert")
	fun chkVarLR (b as (SOME _)) br = b
	  | chkVarLR NONE br =
	    if depends br vrhs andalso not (depends br vlhs)
	      then SOME(ref_nam br) else NONE
	val _ = case foldl chkVarLR NONE lclCxt
		  of NONE => ()
		   | SOME(s) =>
		       (message("reduction RHS mentions variable "^s);
			legoprint vrhs;
			message"reduction LHS does not ";legoprint vlhs;
			failwith"unbound variable in RHS")
      in LabVT(RedPr,vlhs,vrhs)
      end
    and fixEvRed (locs,pairs) cxt =
      let
	val _ = if !eval_debug then red_cache:= (locs,pairs) else ()
	fun er cxt sbst =    (** `CnLst' is a trick for discharge **)
	  ((CnLst(map (fixchkPr (length locs) cxt sbst) pairs),Bot),[])
      in
	fixEvLocs locs er cxt []
      end
    and fixEvCase T branches cxt =
      let
	fun mk1Branch (locs,lhs,rhs) =
	  let
	    fun chkBranch cxt sbst =
	      ((fixchkPr (length locs) cxt sbst (lhs,rhs),T),[])
	  in
	    fixEvLocs locs chkBranch cxt []
	  end
	fun mk2Branch ((v,t),_) =
	  if UMtype_match t T then v
	  else (message"Case body has type "; legoprint T;
		message"Case branch has type "; legoprint t;
		failwith"body and branch types don't convert")
	val branches = map (mk2Branch o mk1Branch) branches
      in CnLst(branches)
      end

  in
    fixfEv V_c Cxt []
  end

in
    fun fixApp V_c = fst (fixApp_ (Namespace.getNamespace()) no_metavars
                          (parser_var_pack()) V_c)
        handle Bungle => failwith "didn't typecheck anayway"
end