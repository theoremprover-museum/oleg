(* conor-voodoo.sml *)
(*
signature VOODOO =
sig
  type voolabel (* = string * int *)
  datatype voodoo =
    Voo of voolabel               (* herein lies the voodoo *)
  | VProp
  | VTheory                                  (* the type of theories *)
  | VType of node
  | VRef of binding
  | VRel of int                                         (* variable *)
  | VApp of (voodoo * (voodoo list)) * (prntVisSort list) (* application *)
  | VBind of bindVisSort * string * voodoo * voodoo
  | VVar of int * voodoo                      (* existential variable *)
  | VTuple of voodoo * (voodoo list)           (* elem of Sig *)
  | VProj of projSort * voodoo
  | VLabVT of label * voodoo * voodoo          (* labeled trm:typ pair *)
  | VCnLst of voodoo list                     (* for use in Theories *)
  | VRedTyp of instrs * voodoo   (* reduce the synthesised type using insts *)
  | VCase of voodoo * voodoo        (* case *)
  | VBot
  type voobind (* = voolabel * bindVisSort * string * voodoo *)
  type vooctxt (* = voobind list *)
  type voostate (* = vooctxt * voodoo *)
  exception too_much_voodoo
  exception missing_voodoo
  exception voodoo_no_rewrite
  val voofold : 'a -> (voolabel -> 'a) -> ('a -> 'a -> 'a) -> voodoo -> 'a
  val voomap : (voolabel -> voodoo) -> voodoo -> voodoo
  val start : cnstr -> voostate
  val introvoo : string -> int -> voostate -> voostate
  val introvool : string list -> int -> int -> voostate -> voostate
  val voo : cnstr -> voodoo
  val unvoo : voodoo -> cnstr
  val stop : voostate -> cnstr
  val outrovoo : voostate -> voodoo
  val vootype : voodoo -> voodoo
  val voorewrite : (voodoo->voodoo)->voodoo->voodoo
  val vooleftmost : (voodoo->voodoo)->voodoo->voodoo
  val voonormal : (voodoo->voodoo)->voodoo->voodoo
  val vooelse : (voodoo->voodoo) list->voodoo->voodoo
  val voolift : (voodoo->voodoo)->voostate->voostate
  val voosub : voolabel -> voodoo -> voostate -> voostate
  val liftrels : int -> voodoo -> voodoo
  val relsub  : voolabel -> voodoo -> int -> voodoo -> voodoo
  val voobeta  : voodoo -> voodoo list -> prntVisSort list -> voodoo
  val voooccur  : voolabel -> voodoo -> bool
  val vooeta  : voodoo -> voodoo
  val shove : voobind -> voolabel -> voostate -> voostate
  val fetch : voolabel -> voostate -> voobind
  val swap : voobind -> voostate -> voostate
  val elide : voolabel -> voostate -> voostate
  val dep1l : voodoo -> voolabel list
  val dep1g : vooctxt -> voolabel -> voolabel list
  val deple : vooctxt -> voolabel -> voolabel list
  val vooprint : voodoo -> unit
  val vooprintstate : voostate -> unit
end
*)
structure Voodoo : VOODOO =
struct
  type voolabel = string * int
  datatype voodoo =
    Voo of voolabel               (* herein lies the voodoo *)
  | VProp
  | VTheory                                  (* the type of theories *)
  | VType of node
  | VRef of binding
  | VRel of int                                         (* variable *)
  | VApp of (voodoo * (voodoo list)) * (prntVisSort list) (* application *)
  | VBind of bindVisSort * string * voodoo * voodoo
  | VVar of int * voodoo                      (* existential variable *)
  | VTuple of voodoo * (voodoo list)           (* elem of Sig *)
  | VProj of projSort * voodoo
  | VLabVT of label * voodoo * voodoo          (* labeled trm:typ pair *)
  | VCnLst of voodoo list                     (* for use in Theories *)
  | VRedTyp of instrs * voodoo   (* reduce the synthesised type using insts *)
  | VCase of voodoo * voodoo        (* case *)
  | VBot
  type voobind = voolabel * bindVisSort * string * voodoo
  type vooctxt = voobind list
  type voostate = vooctxt * voodoo
  exception too_much_voodoo
  exception missing_voodoo
  exception voodoo_no_rewrite

  local
      fun mapsublist P f=
	  let
	      fun msl2 [] = []
		| msl2 (h::t) = if P h then (f h)::(msl2 t) else msl2 t
	  in
	      msl2
	  end
      local
	  exception not_mem
	  fun split i [] = raise not_mem
	    | split i (h::t) = if i=h then ([h],t)
			       else let
					val (l,m) = split i t
				    in
					(h::l,m)
				    end
      in
	  fun merge [] l = l
	    | merge (h::t) l =
	      let
		  val (p,s) = split h l
	      in
		  p@(merge t s)
	      end handle not_mem => h::(merge t l)
      end
  in
      fun voofold i v f =
	  let
	      fun vf (Voo j) = v j
		| vf (VApp ((a,al),_)) = vff (vf a) al
		| vf (VBind (_,_,a,b)) = f (vf a) (vf b)
		| vf (VVar (_,a)) = vf a
		| vf (VTuple (a,al)) = vff (vf a) al
		| vf (VProj (_,a)) = vf a
		| vf (VLabVT (_,a,b)) = f (vf a) (vf b)
		| vf (VCnLst al) = vff i al
		| vf (VRedTyp (_,a)) = vf a
		| vf (VCase (a,b)) = f (vf a) (vf b)
		| vf _ = i
	      and vff x [] = x
		| vff x (h::t) = vff (f x (vf h)) t
	  in
	      vf
	  end
      local
	  fun do_voo              Prop = VProp
	    | do_voo            Theory = VTheory
	    | do_voo          (Type a) = VType a
	    | do_voo           (Ref a) = VRef a
	    | do_voo           (Rel j) = VRel j
	    | do_voo (App ((a,al),vl)) = VApp ((do_voo a,map do_voo al),vl)
	    | do_voo  (Bind (b,s,t,r)) = VBind (b,s,do_voo t,do_voo r)
	    | do_voo       (Var (a,b)) = VVar (a,do_voo b)
	    | do_voo    (Tuple (a,al)) = VTuple (do_voo a,map do_voo al)
	    | do_voo      (Proj (a,b)) = VProj (a,do_voo b)
	    | do_voo   (LabVT (l,a,b)) = VLabVT (l,do_voo a,do_voo b)
	    | do_voo        (CnLst al) = VCnLst (map do_voo al)
	    | do_voo    (RedTyp (a,b)) = VRedTyp (a,do_voo b)
	    | do_voo      (Case (a,b)) = VCase (do_voo a,do_voo b)
	    | do_voo               Bot = VBot
      in
	  fun start c = ([],do_voo c)
      end
      local
	  fun noovoo l =
	      let
		  fun noov i            (Voo j) = Voo j
		    | noov i              VProp = VProp
		    | noov i            VTheory = VTheory
		    | noov i          (VType a) = VType a
		    | noov i           (VRef a) = VRef a
		    | noov i           (VRel j) = if i=j then Voo l
						  else VRel j
		    | noov i (VApp ((a,al),vl)) =
		      VApp ((noov i a,map (noov i) al),vl)
		    | noov i  (VBind (b,s,t,r)) = VBind (b,s,noov i t,
							 noov (i+1) r)
		    | noov i       (VVar (a,b)) = VVar (a,noov i b)
		    | noov i    (VTuple (a,al)) =
		      VTuple (noov i a,map (noov i) al)
		    | noov i      (VProj (a,b)) = VProj (a,noov i b)
		    | noov i   (VLabVT (l,a,b)) = VLabVT (l,noov i a,noov i b)
		    | noov i        (VCnLst al) = VCnLst (map (noov i) al)
		    | noov i    (VRedTyp (a,b)) = VRedTyp (a,noov i b)
		    | noov i      (VCase (a,b)) = VCase (noov i a,noov i b)
		    | noov i               VBot = VBot
	      in
		  noov 1
	      end
	  fun intro1 (s,i) (vl,(VBind (b,nam,t,r))) =
	      let
		  val nam' = if nam="" then s^(string_of_num i) else nam
	      in
		  (vl@[((s,i),b,nam',t)],noovoo (s,i) r)
	      end
	    | intro1 _ _ = raise too_much_voodoo
          fun introl i [] S = S
            | introl i (h::t) S = introl i t (intro1 (h,i) S)
      in
	  fun introvoo s 0 S = S
	    | introvoo s n S = intro1 (s,n) (introvoo s (n-1) S)
          fun introvool l i 0 S = S
            | introvool l i n S = introl (i+n-1) l (introvool l i (n-1) S)
      end
      fun voo c = #2 (start c)
(*
      fun stop (vc,vt) =
	  let
	      fun get done i =
		  let
		      fun g2 _ [] = raise missing_voodoo
			| g2 j (h::t) = if i=h then j
					else g2 (j+1) t
		  in
		      g2 1 done
		  end
	      fun un_voo g =
		  let
		      fun uv i (Voo j) = Rel (i+(g j))
			| uv i VProp = Prop
			| uv i VTheory = Theory
			| uv i (VType a) = Type a
			| uv i (VRef a) = Ref a
			| uv i (VRel j) = Rel j
			| uv i (VApp ((a,al),vl)) =
		          App ((uv i a,map (uv i) al),vl)
			| uv i (VBind (b,s,t,r)) =
			  Bind (b,s,uv i t,uv (i+1) r)
			| uv i (VVar (a,b)) = Var (a,uv i b)
			| uv i (VTuple (a,al)) =
			  Tuple (uv i a,map (uv i) al)
			| uv i (VProj (a,b)) = Proj (a,uv i b)
			| uv i (VLabVT (l,a,b)) =
			  LabVT (l,uv i a,uv i b)
			| uv i (VCnLst al) = CnLst (map (uv i) al)
			| uv i (VRedTyp (a,b)) = RedTyp (a,uv i b)
			| uv i (VCase (a,b)) =
			  Case (uv i a,uv i b)
			| uv i VBot = Bot
		  in
		      uv
		  end
	      fun rebind done [] = un_voo (get done) 0 vt
		| rebind done ((i,b,s,t)::r) =
		  Bind (b,s,un_voo (get done) 0 t,
			rebind (i::done) r)
	  in
	      rebind [] vc
	  end
*)
      fun outrovoo (vc,vt) =
	  let
	      fun get done i =
		  let
		      fun g2 _ [] = raise missing_voodoo
			| g2 j (h::t) = if i=h then j
					else g2 (j+1) t
		  in
		      g2 1 done
		  end
	      fun un_voo g =
		  let
		      fun uv i (Voo j) =
                          (VRel (i+(g j))
                           handle missing_voodoo => Voo j)
			| uv i (VApp ((a,al),vl)) =
		          VApp ((uv i a,map (uv i) al),vl)
			| uv i (VBind (b,s,t,r)) =
			  VBind (b,s,uv i t,uv (i+1) r)
			| uv i (VVar (a,b)) = VVar (a,uv i b)
			| uv i (VTuple (a,al)) =
			  VTuple (uv i a,map (uv i) al)
			| uv i (VProj (a,b)) = VProj (a,uv i b)
			| uv i (VLabVT (l,a,b)) =
			  VLabVT (l,uv i a,uv i b)
			| uv i (VCnLst al) = VCnLst (map (uv i) al)
			| uv i (VRedTyp (a,b)) = VRedTyp (a,uv i b)
			| uv i (VCase (a,b)) =
			  VCase (uv i a,uv i b)
                        | uv i x = x
		  in
		      uv
		  end
	      fun rebind done [] = un_voo (get done) 0 vt
		| rebind done (((l,n),b,s,t)::r) =
		  VBind (b,if s="" then (l^(string_of_num n))
                           else s,un_voo (get done) 0 t,
			rebind ((l,n)::done) r)
	  in
	      rebind [] vc
	  end
      fun unvoo (Voo j) = raise missing_voodoo
	| unvoo VProp = Prop
	| unvoo VTheory = Theory
	| unvoo (VType a) = Type a
	| unvoo (VRef a) = Ref a
	| unvoo (VRel j) = Rel j
	| unvoo (VApp ((a,al),vl)) = App ((unvoo a,map unvoo al),vl)
	| unvoo (VBind (b,s,t,r)) = Bind (b,s,unvoo t,unvoo r)
	| unvoo (VVar (a,b)) = Var (a,unvoo b)
	| unvoo (VTuple (a,al)) = Tuple (unvoo a,map unvoo al)
	| unvoo (VProj (a,b)) = Proj (a,unvoo b)
	| unvoo (VLabVT (l,a,b)) = LabVT (l,unvoo a,unvoo b)
	| unvoo (VCnLst al) = CnLst (map unvoo al)
	| unvoo (VRedTyp (a,b)) = RedTyp (a,unvoo b)
	| unvoo (VCase (a,b)) = Case (unvoo a,unvoo b)
	| unvoo VBot = Bot
      fun stop S = unvoo (outrovoo S)
      fun vootype v = voo ((!toc) (stop ([],v)))
      fun voorewrite f =
	  let
	      fun hit v = (f v) handle voodoo_no_rewrite => split v
	      and split (VApp ((v,vl),pl)) = VApp ((hit v,map hit vl),pl)
		| split (VBind (b,s,u,v)) = VBind (b,s,hit u,hit v)
		| split (VVar (i,v)) = VVar (i,hit v)
		| split (VTuple (v,vl)) = VTuple (hit v,map hit vl)
		| split (VProj (p,v)) = VProj (p,hit v)
		| split (VLabVT (l,u,v)) = VLabVT (l,hit u,hit v)
		| split (VCnLst vl) = VCnLst (map hit vl)
		| split (VRedTyp (i,v)) = VRedTyp (i,hit v)
		| split (VCase (u,v)) = VCase (hit u,hit v)
		| split v = v
	  in
	      hit
	  end

      fun vooleftmost f =
          let fun hit v = (f v) handle voodoo_no_rewrite => split v
              and split (VApp ((v,vl),pl)) =
                 (VApp ((hit v,vl),pl)
                  handle voodoo_no_rewrite =>
                  VApp ((v,hitlist vl),pl))
                | split (VBind (b,s,u,v)) =
                 (VBind (b,s,hit u,v)
                  handle voodoo_no_rewrite =>
                  VBind (b,s,u,hit v))
                | split (VVar (i,v)) = VVar (i,hit v)
                | split (VTuple (v,vl)) =
                 (VTuple (hit v,vl)
                  handle voodoo_no_rewrite =>
                  VTuple (v,hitlist vl))
                | split (VProj (p,v)) = VProj (p,hit v)
                | split (VLabVT (l,u,v)) =
                 (VLabVT (l,hit u,v)
                  handle voodoo_no_rewrite =>
                  VLabVT (l,u,hit v))
                | split (VCnLst vl) = VCnLst (hitlist vl)
                | split (VRedTyp (i,v)) = VRedTyp (i,hit v)
                | split (VCase (u,v)) =
                 (VCase (hit u,v)
                  handle voodoo_no_rewrite =>
                  VCase (u,hit v))
                | split v = raise voodoo_no_rewrite
              and hitlist [] = raise voodoo_no_rewrite
                | hitlist (h::t) = ( (hit h)::t
                                     handle voodoo_no_rewrite =>
                                     h::(hitlist t) )
          in  hit
          end

      fun vooelse [] x = raise voodoo_no_rewrite
        | vooelse (f::t) x = f x
          handle voodoo_no_rewrite => vooelse t x

      fun voonormal f x =
          voonormal f (vooleftmost f x)
          handle voodoo_no_rewrite => x

      fun voolift f (vc,vt) =
	  let
	      fun fc [] = []
		| fc ((i,b,s,h)::t) = (i,b,s,f h)::(fc t)
	  in
	      (fc vc,f vt)
	  end
      fun voomap v =
	  let
	      fun vm (Voo j) = v j
		| vm _ = raise voodoo_no_rewrite
	  in
	      voorewrite vm
	  end
      fun voosub i v =
	  voolift (voomap (fn j => if i=j then v else (Voo j)))
      fun liftrels j =
          let fun lr2 i (v as VRel k) = if k>i then VRel (k+j) else v
                | lr2 i (VBind (b,s,u,v)) =
                  VBind (b,s,voorewrite (lr2 i) u,voorewrite (lr2 (i+1)) v)
                | lr2 _ _ = raise voodoo_no_rewrite
          in  voorewrite (lr2 0)
          end
      fun relsub i v n =
          let fun rs2 k (u as Voo j) = if i=j then liftrels k v else u
                | rs2 k (VBind (b,s,p,q)) =
                  VBind (b,s,voorewrite (rs2 k) p,voorewrite (rs2 (k+1)) q)
                | rs2 k _ = raise voodoo_no_rewrite
          in  voorewrite (rs2 n)
          end
      fun voobeta (f as VBind ((Lda,_),_,_,_)) (ah::at) (_::vt) =
          let val (_,body) = introvool ["fred"] 1 1 ([],f)
              val knockoff = liftrels (~1) body
          in  voobeta (relsub ("fred",1) ah 0 knockoff) at vt
          end
        | voobeta f [] _ = f
        | voobeta f args vis = VApp ((f,args),vis)
 
      fun voooccur v t = voofold false (fn u => u=v)
                                 (fn b => fn c => b orelse c) t
      fun splitlast [h] = ([],h)
        | splitlast (h::t) = let val (l,x) = splitlast t in (h::l,x) end
        | splitlast [] = raise Match

      fun shove (bind as (_,_,_,ty)) leftStop (pref,tail) =
          let fun later i j = if i=j then i else
                  let fun search1 fnd nfnd [] = fnd
                        | search1 fnd nfnd ((h,_,_,_)::t) =
                          if h=nfnd then nfnd else search1 fnd nfnd t
                      fun search2 [] = i
                        | search2 ((h,_,_,_)::t) =
                          if h=i then search1 i j t
                          else if h=j then search1 j i t
                               else search2 t
                  in  search2 pref
                  end
              val where = voofold leftStop (fn i => i) later ty
              fun doit [] = raise Match
                | doit ((h as (i,_,_,_))::t) = if i=where then h::bind::t
                                               else h::(doit t)
          in  (doit pref handle Match => bind::pref,tail)
          end
(*
      fun shove (x as (i,b,s,v)) rightofhere (vc,vt) =
	  let
	      fun righter j k =
		  if j=i then k
		  else if k=i then j
		       else
			   let
			       fun r2 [] = raise missing_voodoo
				 | r2 ((l,_,_,_)::t) =
				   if j=l then k
				   else if k=l then j
					else r2 t
			   in
			       r2 vc
			   end
	      val where = voofold rightofhere (fn j => j) righter v
	      fun go [] = raise missing_voodoo
		| go ((h as (j,_,_,_))::t) =
		  if j=where then h::x::t else h::(go t)
	  in
	      if where=i then (x::vc,vt)
	      else (go vc,vt)
	  end
*)
      fun fetch i (vc,_) =
	  let
	      fun f2 [] = raise missing_voodoo
		| f2 ((h as (j,_,_,_))::t) =
		  if i=j then h else f2 t
	  in
	      f2 vc
	  end
      fun swap (x as (i,_,_,_)) (vc,vt) =
	  let
	      fun s2 [] = raise missing_voodoo
		| s2 ((h as (j,_,_,_))::t) =
		  if i=j then x::t else h::(s2 t)
	  in
	      (s2 vc,vt)
	  end
      fun elide i (vc,vt) =
	  let
	      fun e2 [] = raise missing_voodoo
		| e2 ((h as (j,_,_,_))::t) =
		  if i=j then t else h::(e2 t)
	  in
	      (e2 vc,vt)
	  end
      fun vooeta f =
          let fun ein i (S as (_,(VBind ((Lda,_),_,_,t)))) =
                  ein (i+1) (introvool ["etatest"] i 1 S)
                | ein i S = S
              val inldas = ein 1 ([],f)
              val nldas = length (#1 inldas)
              fun doit 0 S = S
                | doit n (S as (ldas,VApp ((g,rs),vs))) =
                 (let val (frs,r) = splitlast rs
                      val (fvs,v) = splitlast vs
                      val M = case frs
                                of [] => g
                                 | _  => VApp ((g,frs),fvs)
                  in if r=(Voo ("etatest",n)) andalso 
                        not (voooccur ("etatest",n) M)
                         then doit (n-1) (elide ("etatest",n) (ldas,M))
                     else S
                  end
                  handle Match => S)
                | doit _ S = S
          in  outrovoo (doit nldas inldas)
          end

      val dep1l = voofold [] (fn x => [x]) (fn l => fn m => l@m)
      fun dep1g C i =
	  mapsublist
	  ((voofold false (fn j => i=j) (fn a => fn b => a orelse b)) o
	   (fn (_,_,_,t) => t))
	  (fn (i,_,_,_) => i)
	  C
      local
	  fun mem i [] = false
	    | mem i (h::t) = i=h orelse mem i t
      in
	  fun deple [] = (fn k => [k])
	    | deple ((h as (n,_,_,_))::t) =
	      let
		  val prev = deple t
		  fun next l j = 
		      let
			  val pj = prev j
			  fun n2 [] = pj
			    | n2 (i::u) = if mem i pj then n::pj
					  else n2 u
		      in
			  n2 l
		      end
	      in
		  next (dep1g t n)
	      end
      end
      fun vooprint (Voo (s,j)) = ((print ("V-"^s));(print j))
	| vooprint VProp = print "Prop"
	| vooprint VTheory = print "Theory"
	| vooprint (VType a) = print "Type(?)"
	| vooprint (VRef a) = print (ref_nam a)
	| vooprint (VRel j) = ((print "R");(print j))
	| vooprint (VApp ((a,al),vl)) =
	  ((print "(");(vooprint a);
	   (map (fn x => ((print " ");(vooprint x))) al);(print ")"))
	| vooprint (VBind ((b,_),s,t,r)) =
	  ((case b of
		Pi => ((print ("{"^s^":"));(vooprint t);(print "}"))
	      | Lda => ((print ("["^s^":"));(vooprint t);(print "]"))
	      | Sig => ((print ("<"^s^":"));(vooprint t);(print ">"))
	      | _ => ((print ("!"^s^":"));(vooprint t);(print "!")));
		(vooprint r))
	| vooprint (VVar (a,b)) = ((print "(?");(print a);(print ":");
	                           (vooprint b);(print ")"))
	| vooprint (VTuple (a,al)) =
	  ((print "(");(vooprint (hd al));
	   (map (fn x => ((print ",");(vooprint x))) (tl al));
	   (print ")"))
	| vooprint _ = print "!"
      fun vooprintstate ([],vt) =
	  ((print "tail : ");(vooprint vt);(print "\n"))
	| vooprintstate (((s:string,i:int),(b,_),nam,u)::t,vt) =
	  ((print s);(print i);
	   (print (case b of Pi => " P" | Lda => " L" |
                             Sig => " S" | _ => " !"));
	   (print (" "^nam^" : "));(vooprint u);(print "\n");
	   (vooprintstate (t,vt)))
  end
end
