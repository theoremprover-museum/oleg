

      exception noQnify

      fun howManyIntros g =
          let val eqBd = case (#1 (Require ["Eq"]))
                           of Ref b => b
                            | _ => raise noQnify
              val (h,t) = case weakHeadRed g
                            of Bind ((Pi,_),_,h,t) => (h,t)
                             | _ => raise noQnify
          in  case weakHeadRed h
                of App ((Ref q',[_,_,_]),_) =>
                   if sameRef q' eqBd then 1
                   else 1+(howManyIntros t)
                 | _ => 1+howManyIntros t
          end

      fun thatManyIntros n =
          let val _ = Intros (~9999) true (mkList (fn _ => "") 1 n)
                      handle _ => raise noQnify
              val q = Ref (hd (getNamespace ()))
          in  (q,type_of_constr q)
          end

      fun tryList l a =
          let fun tryl [] = 0         (* ie added no new equations *)
                | tryl (f::t) = f a
                  handle noQnify => tryl t
          in  tryl l
          end

      fun parseApp x =
          let fun pa2 (App ((f,a'),v')) a v = pa2 f (a'@a) (v'@v)
                | pa2 x a v = (x,a,v)
          in  pa2 x [] []
          end

      fun namdepts (Ref (Bd {deps=cl,
                             bd=(_,s,_,_),
                             ts=t,...})) = (s,cl,t)
        | namdepts _ = raise noQnify

      fun vnamdepts (VRef (Bd {deps=cl,
                             bd=(_,s,_,_),
                             ts=t,...})) = (s,cl,t)
        | vnamdepts _ = raise noQnify

      fun howManyJecs conName typeName =
          let val params = #1 (choppec (parselim (voo (#2 (Require
                                                [typeName,"cases"])))))
              val rawArgs = voobdep (voo (#2 (fEval (Ref_c conName))))
          in  rawArgs-(length params)
          end

      fun appNoConf theThm itsType theHyp thePsi =
          let val depth = voobdep itsType
              val front = mkVl "guess" 1 (depth-2)
              val priorArgs = front@[theHyp,thePsi]
              val (_,v) = ArgsAndVis
                          (#1 (introvool ["splat"] 1 depth ([],itsType)))
                          ([],[])
              val (f,a) = voosynth [] (theThm,priorArgs)
          in  VApp((f,a),v)
          end

      fun cons1 h (a,b) = (h::a,b)

      fun ctxtSplit id [] = raise missing_voodoo
        | ctxtSplit id ((h as (jd,_,_,_))::t) =
          if id=jd then ([],t) else cons1 h (ctxtSplit id t)

      fun vooK id (T,L,R) goal =
          if voowrap (#1 (ctxtSplit id (#1 goal)))
                     (fn rew => fn (u,v) => (unvoo (rew u),unvoo (rew v)))
                     (fn (x,y) => sameTerm x y)
                     (fn _ => fn b => b)
                     (L,R)
          then
         (let val (_,_,subGoals,lambdaThese,theTrick) =
                  elimClobberPlan true [] (vooreq ["Eq","K"]) goal (Voo id)
              val solveGoal = vooeta (outrovoo (map vooPiToLda lambdaThese,
                                                theTrick))
          in  (0,(subGoals,solveGoal))
          end
          handle _ => raise noQnify)
          else raise noQnify

      fun qK (H,(T,L,R)) =
          if sameTerm L R
          then
         (let val (K,_) = Require ["Eq","K"]
              val (nH,_ ,tH) = namdepts H
              val vgoal = voo (#2 (goaln (~9999)))
              val Psi = stop (refAbstract [(tH,("e",1))]
                              ([(("e",1),(Lda,Vis),nH,voo (type_of_constr H))],
                               vgoal))
              val _ = Refine (~9999) 0 (App_c (ShowNorm,
                                        App_c (ShowNorm,unEval K,
                                                        unEval H),
                                                        unEval Psi))
          in  0
          end
          handle _ => raise noQnify)
          else raise noQnify

      fun vooJ id (T,L,R) goal =
         (let val (Rid,i) = case R
                              of Voo (Rid as ("q",i)) => (Rid,i)
                               | _ => raise noQnify
              val _ = if (voooccur Rid L) then raise noQnify
                      else case L
                             of Voo ("q",j) =>
                                if i<j then raise noQnify else ()
                              | _ => ()
              val (_,_,subGoals,lambdaThese,theTrick) =
                  elimClobberPlan true [] (vooreq ["Eq","J"]) goal (Voo id)
              val solveGoal = vooeta (outrovoo (map vooPiToLda lambdaThese,
                                                theTrick))
          in  (0,(subGoals,solveGoal))
          end
          handle _ => raise noQnify)

      fun qJ (H,(T,L,R)) =
         (let val (J,_) = Require ["Eq","J"]
              val (nR,_ ,tR) = namdepts R
              val (nH,_ ,tH) = namdepts H
              fun checkem (Ref (Bd {ts=tL,...})) (Ref b) =
                  if tL>=tR then raise noQnify else ()
                | checkem L (Ref b) =
                  if depends b L (* lazy and maybe dodgy *)
                  then raise noQnify else ()
                | checkem _ _ = raise noQnify
              val _ = checkem L R
              val vgoal = voo (#2 (goaln (~9999)))
              val Phi = stop (refAbstract [(tR,("q",1)),(tH,("e",1))]
                              ([(("q",1),(Lda,Hid),nR,voo T),
                                (("e",1),(Lda,Vis),nH,voo (type_of_constr H))],
                               vgoal))
              val _ = Refine (~9999) 0 (App_c (ShowNorm,
                                        App_c (ShowNorm,unEval J,
                                                        unEval H),
                                                        unEval Phi))
          in  0
          end
          handle _ => raise noQnify)

      fun vooJsym id (T,L,R) goal =
         (let val (Lid,i) = case L
                              of Voo (Lid as ("q",i)) => (Lid,i)
                               | _ => raise noQnify
              val _ = if (voooccur Lid R) then raise noQnify
                      else case R
                             of Voo ("q",j) =>
                                if i<j then raise noQnify else ()
                              | _ => ()
              val (_,_,subGoals,lambdaThese,theTrick) =
                  elimClobberPlan true [] (vooreq ["Eq","J","sym"])
                                  goal (Voo id)
              val solveGoal = vooeta (outrovoo (map vooPiToLda lambdaThese,
                                                theTrick))
          in  (0,(subGoals,solveGoal))
          end
          handle _ => raise noQnify)

      fun qJsym (H,(T,L,R)) =
         (let val (J,_) = Require ["Eq","J","sym"]
              val (nL,_ ,tL) = namdepts L
              val (nH,_ ,tH) = namdepts H
              fun checkem (Ref b) (Ref (Bd {ts=tR,...})) =
                  if tR>=tL then raise noQnify else ()
                | checkem (Ref b) R =
                  if depends b R (* lazy and maybe dodgy *)
                  then raise noQnify else ()
                | checkem _ _ = raise noQnify
              val _ = checkem L R
              val vgoal = voo (#2 (goaln (~9999)))
              val Phi = stop (refAbstract [(tL,("q",1)),(tH,("e",1))]
                              ([(("q",1),(Lda,Hid),nL,voo T),
                                (("e",1),(Lda,Vis),nH,voo (type_of_constr H))],
                               vgoal))
              val _ = Refine (~9999) 0 (App_c (ShowNorm,
                                        App_c (ShowNorm,unEval J,
                                                        unEval H),
                                                        unEval Phi))
          in  0
          end
          handle _ => raise noQnify)

      fun vooRigidRigid id (T,L,R) (goalP,goalT) =
         (let val (fT,aT,vT) = vooparseapp T
              val (fL,_,_) = vooparseapp L
              val (fR,_,_) = vooparseapp R
              val (nT,cT,_ ) = vnamdepts fT
              val (nL,_ ,_ ) = vnamdepts fL
              val (nR,_ ,_ ) = vnamdepts fR
              val _ = if      (member nL cT)
                      andalso (member nR cT)
                      then ()
                      else raise noQnify
              val (no_conf,itsType) = Require [nT,"no","confusion"]
              val vnc = voo no_conf
              val vitsty = voo itsType
              fun cutup [] = raise noQnify
                | cutup ((h as (jd,_,_,_))::t) =
                  if jd=id then ([h],(vooPiToLda h)::t)
                  else let val (f,b) = cutup t
                       in  (h::f,b)
                       end
              val (front,back) = cutup goalP
              val Psi = outrovoo (back,goalT)
              val dep = (voobdep vitsty)
              val priors = (mkVl "bog" 1 (dep-2))@[Voo id,Psi]
              val (_,v) = ArgsAndVis
                          (#1 (introvool ["splat"] 1 dep ([],vitsty)))
                          ([],[])
              val (f,a) = voosynth front (vnc,priors)
              val trick = VApp ((f,a),v)
              val hnfTy = voowrap front construe (whnf o type_of_constr)
                                  review trick
              val (newSubg,newTail) = introvool ["subgoal"] 1 1 ([],hnfTy)
              val trickApp = flApp ((trick,[Voo ("subgoal",1)]),[NoShow])
          in  if nL=nR
              then (* it's injectivity *)
              let val allBut = vooctxtelide id front
                  val nearly = (newSubg,trickApp)
                  val (subgs,protoPf) =
                      foldr (fn (id,_,_,_) => fn S =>
                                promoteEquations id 
                                (genova allBut id S))
                            nearly newSubg
                  val theProof = outrovoo (map vooPiToLda front,protoPf)
                  val thePlan = (subgs,theProof)
              in  (howManyJecs nL nT,thePlan)
              end
              else (* it's conflict *)
              let val nearly = (newSubg,
                                outrovoo (map vooPiToLda front,trickApp))
              in  (0,voosolve ("subgoal",1)
                           (voobeta Psi [Voo id] [ShowNorm]) nearly)
              end
          end
          handle _ => raise noQnify)

      fun qRigidRigid (H,(T,L,R)) =
         (let val (fT,aT,vT) = parseApp T
              val (fL,_,_) = parseApp L
              val (fR,_,_) = parseApp R
              val (nT,cT,_ ) = namdepts fT
              val (nL,_ ,_ ) = namdepts fL
              val (nR,_ ,_ ) = namdepts fR
              val (nH,_ ,tH) = namdepts H
              val _ = if      (member nL cT)
                      andalso (member nR cT)
                      then ()
                      else raise noQnify
              val (no_conf,itsType) = Require [nT,"no","confusion"]
              val vgoal = voo (#2 (goaln (~9999)))
              val Psi = outrovoo
                             (refAbstract [(tH,("e",1))]
                              ([(("e",1),(Lda,Vis),nH,voo (type_of_constr H))],
                               vgoal))
              val byThis = unEval (unvoo (appNoConf (voo no_conf)
                                                    (voo itsType)
                                                    (voo H)
                                                    Psi))
              val _ = Refine (~9999) 0 byThis
          in  if nL=nR then howManyJecs nL nT
              else ~9999
          end
          handle _ => raise noQnify)

      val voonifyTacs = ref [vooK,vooJ,vooJsym,vooRigidRigid]

      fun vootryTacs id bits G =
          let fun try [] = raise noQnify
                | try (h::t) = h id bits G
                               handle noQnify => try t
          in  try (!voonifyTacs)
          end

      local
          val protCounter = ref 0
          fun introList [] S = S
            | introList ((s,i)::t) S =
              introList t (introvool [s] i 1 S)
      in  fun vooprotect (P:vooctxt,T) =
              let val oldNames = map (#1) P
                  val addOn = length P
                  val old = !protCounter
                  val _ = protCounter := old+addOn
                  val (P,T) = introvool ["protect"] old addOn
                              ([],outrovoo (P,T))
                  val newNames = map (#1) P
              in  (ListUtil.zip (newNames,oldNames),(P,T))
              end
          fun voounprotect alist (S as (P,T)) =
              introList (map (fn (id,_,_,_) =>
                                 assoc id alist
                                 handle Assoc => id) P) 
                        ([],outrovoo S)
      end

      fun app1 l (x,y) = (l@x,y)

      local
          val eqBd = ref (Bd {kind=Bnd,ts=0,frz=ref UnFroz,param=Local,deps=[],
                              bd=((Pi,Vis),"bogus",Bot,Bot)})
          val voowh = voo o weakHeadRed o unvoo
          fun voodointros n (gP,gT) =
              let val (v,s,h,t) =
                      case voowh gT
                        of VBind ((Pi,v),s,h,t) => (v,s,h,t)
                         | _ => raise noQnify
                  val h = voowh h
                  val G = introvool ["q"] n 1 (gP,VBind ((Pi,v),s,h,t))
                  val qn = ("q",n)
              in (case voowh h
                    of VApp ((VRef q',[T,L,R]),_) =>
                       if sameRef q' (!eqBd)
                       then (qn,(voowh T,voowh L,voowh R),G)
                       else raise Match
                     | _ => raise Match)
                  handle Match =>
                  voowrap [last (#1 G)]
                          (fn rew => fn (P,T) => (P,rew T))
                          (voodointros (n+1))
                          (fn rew => fn (id,(T,L,R),G) =>
                              (id,(rew T,rew L,rew R),voolift rew G))
                          G
              end
          fun dovoonify 0 goal = ([(("subgoal",1),(Pi,Vis),"",goal)],
                                  Voo ("subgoal",1))
            | dovoonify n goal =
             (let val (id,bits,goal) = voodointros 1 ([],goal)
                  val (nNew,(subGoals,trick)) = vootryTacs id bits goal
              in  case subGoals
                    of [] => ([],trick) (* we won *)
                     | [(sid,_,_,subgoal)] => (* 'nother go, maybe *)
                       let val n = if n<0 then n
                                    else n-1+nNew
                           val (S,T) = dovoonify n subgoal
                       in  (S,voorewrite (vooblat sid T) trick)
                       end
                     | _ => bug "more than one subgoal in voonify"
              end
              handle noQnify => dovoonify 0 goal)
      in  fun voonify n id (S as (SP,ST)) =
              let val (protectData,S as (SP,stuff)) =
                      vooprotect (SP,VCnLst [ST,Voo id])
                  val (ST,id) = case stuff
                                  of VCnLst [ST,Voo id] => (ST,id)
                                   | _ => bug "protection racket"
                  val _ = eqBd :=(case (#1 (Require ["Eq"]))
                                    of Ref b => b
                                     | _ => raise noQnify)
                  val (fore,aft) = ctxtSplit id SP
                  val (_,bv,nam,subGoal) = fetch id S
                  val (subgS,trick) = 
                      voowrap fore (fn rew => rew) (dovoonify n) voolift 
                              subGoal
              in  voounprotect protectData
                 (case subgS
                    of [] =>
                       let val rew = voorewrite (vooblat id trick)
                       in  app1 fore (voolift rew (aft,ST))
                       end
                     | [(sid,_,_,subgtype)] =>
                       let val rew = voorewrite (vooblat id trick)
                       in  voorename sid id
                          (app1 (fore@[(sid,bv,nam,subgtype)])
                                (voolift rew (aft,rew ST)))
                       end
                     | _ => bug "more than one subgoal in voonify")
              end
      end

      fun findPrem c i goal =
          let exception shesNotThere
              val s = case c
                        of Ref_c s => s
                         | _ => ""
              fun get_name n (Bind ((Pi,_),s',_,r)) =
                  if s=s' then n
                  else get_name (n+1) r
                | get_name _ _ = raise shesNotThere (* how would I know? *)
              fun get_num k m (Bind ((Pi,_),w,_,r)) =
	          if (var_occur r) then get_num (k+1) m r
	          else if m=i then k
		       else get_num (k+1) (m+1) r
	        | get_num _ _ _ = failwith
                                  "there aren't that many (..)-> premises"
              val vgoal = start goal
          in  let val howMany = (case i
                                   of 0 => get_name 1
                                    | i => get_num 1 1)   goal
              in  (introvool ["q"] 1 howMany (start goal),Voo ("q",howMany))
              end
              handle shesNotThere => (vgoal,voo (#1 (fEval c)))
          end

      fun DedicatedTac c i tagTail =
          let val _ = if (activeProofState()) then ()
                      else failwith "Not in active proof state"
              val goal = #2 (goaln (~9999))
              val (vgoal,target) = findPrem c i goal
              val eTypeName =
                  case #1 (vooparseapp
                       (voowrap (#1 vgoal)
                        construe (whnf o type_of_constr) review target))
                    of VRef (Bd {bd=(_,tn,_,_),...}) => tn
                     | _ => failwith "Couldn't find type"
              val rule = vooreq (eTypeName::tagTail)
          in  tactic_wrapper
              (fn () => applyPlan (elimClobberGen [] rule vgoal target))
              ()
          end
(**)
  in
(**)

      type cnstr_c = cnstr_c

      exception noQnify = noQnify

      val qtacs = ref ([qK,qRigidRigid,qJ,qJsym
                        ]:((cnstr*(cnstr*cnstr*cnstr))->int) list)

      fun qnifyOneStep () =
          let val goal = #2 (goaln (~9999))
              val nIn = howManyIntros goal
              val (eqHyp,eqType) = thatManyIntros nIn
              val TLR =
                  case weakHeadRed eqType
                    of App ((_ (* know this is Eq *),
                             [t,l,r]),_) =>
                       (weakHeadRed t,
                        weakHeadRed l,
                        weakHeadRed r)
                     | _ => ((message "qnify eq recognition dodgy!");
                             (raise noQnify))
          in  tryList (!qtacs)
                 (eqHyp,TLR)
          end

      fun KJunify 0 = ()
        | KJunify n =
          ((case qnifyOneStep ()
              of (~9999) => ()
               | newEqs => KJunify
                           (if n>=0 then n-1+newEqs
                            else n))
           handle noQnify => ())
    