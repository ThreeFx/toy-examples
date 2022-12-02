theory SimplyTypedLambdaCalculus

imports Main

begin

type_synonym var = string

no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)

datatype type = TUnit
  | TApp type type ("_ \<rightarrow> _")

datatype expr =
    Unit
  | Var var
  | Abs var type expr
  | App expr expr

(* it is important to choose a list here, since this defines how the type lookup is made
   when augmenting the context *)
type_synonym ctx = "(var \<times> type) list"

fun has_type_in_ctx :: "var \<times> type \<Rightarrow> ctx \<Rightarrow> bool" ("(_ \<in> _)" [51, 51] 50) where
  "has_type_in_ctx    _          [] = False" |
  "has_type_in_ctx (x,\<tau>) ((y,\<tau>')#\<Gamma>) = (if x = y then \<tau> = \<tau>' else has_type_in_ctx (x,\<tau>) \<Gamma>)"

inductive "value" :: "expr \<Rightarrow> bool" where
  ValueUnit: "value Unit"
| ValueFn: "value (Abs x t e1)"

declare value.intros[simp,intro]

fun fvs :: "expr \<Rightarrow> var set" where
  "fvs Unit          = {}" |
  "fvs (Var v)       = {v}" |
  "fvs (Abs x ty e)  = fvs e - {x}" |
  "fvs (App e1 e2)   = fvs e1 \<union> fvs e2"

fun subst :: "var \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst x t Unit         = Unit" |
  "subst x t (Var v)      = (if x = v then t else Var v)" |
  "subst x t (Abs v ty e) = Abs v ty (if x = v then e else subst x t e)" |
  "subst x t (App e1 e2)  = App (subst x t e1) (subst x t e2)"

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" where
  CApp1: "reduce e1 e1' \<Longrightarrow> reduce (App e1 e2) (App e1' e2)"
| CApp2: "value e1      \<Longrightarrow> reduce e2 e2' \<Longrightarrow> reduce (App e1 e2) (App e1 e2')"
| RApp:  "value e2      \<Longrightarrow> reduce (App (Abs x ty e1) e2) (subst x e2 e1)"

declare reduce.intros[simp,intro]

inductive_cases ReduceAppE[elim]: "reduce (App e1 e2) e"
inductive_cases ReduceElimE[elim]: "reduce (Let x e1 e2) e"

inductive has_type :: "ctx \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _" [40,40,40]) where
  TypeUnit: "\<Gamma> \<turnstile> Unit : TUnit" |
  TypeVar:  "(x, \<tau>) \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>" |
  TypeFn:   "\<lbrakk> ((x, \<tau>)#\<Gamma>) \<turnstile> e : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Abs x \<tau> e) : (\<tau> \<rightarrow> \<tau>')" |
  TypeApp:  "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>' \<rightarrow> \<tau>); \<Gamma> \<turnstile> e2 : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App e1 e2) : \<tau>"

declare has_type.intros[simp,intro]

inductive_cases TypeUnitE[elim!]: "\<Gamma> \<turnstile> Unit : \<tau>"
inductive_cases TypeVarE[elim!]:  "\<Gamma> \<turnstile> (Var x) : \<tau>"
inductive_cases TypeFnE[elim]:    "\<Gamma> \<turnstile> (Abs x \<tau> e) : \<tau>"
inductive_cases TypeAppE[elim]:   "\<Gamma> \<turnstile> (App e1 e2) : \<tau>"

inductive step_or_value where
  IsValue: "value e \<Longrightarrow> step_or_value e" |
  IsStep: "\<exists>e'. reduce e e' \<Longrightarrow> step_or_value e"

declare step_or_value.intros[simp,intro]

inductive_cases StepOrValueE[elim!]: "step_or_value e"

lemma subst_identity[simp]:
  "subst x (Var x) e = e"
  by (induct e, auto)

lemma identity_exists:
  "value e \<Longrightarrow> reduce (App (Abs x \<tau> (Var x)) e) e"
  (* found by sledgehammer *)
  by (metis RApp subst.simps(2))

theorem progress:
  "[] \<turnstile> e : \<tau> \<Longrightarrow> step_or_value e"
proof (induction  "[] :: ctx" "e" "\<tau>" rule:has_type.induct)
  case (TypeApp e1 \<tau>' \<tau> e2)
  then show ?case
    (* found by sledgehammer *)
    using step_or_value.simps value.simps by auto
qed auto

lemma context_strengthening:
  "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> \<forall>x \<tau>'. Set.member x (fvs e) \<longrightarrow> (x, \<tau>') \<in> \<Gamma> \<longrightarrow> (x, \<tau>') \<in> \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> e : \<tau>"
proof (induction arbitrary: \<Gamma>' rule: has_type.induct)
  case (TypeApp \<Gamma> e1 \<tau>' \<tau> e2)
  then show ?case
    (* found by sledgehammer *)
    by (metis Un_iff fvs.simps(4) has_type.TypeApp)
qed auto

lemma well_typed_fvs:
  "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> \<forall>v \<in> fvs e. (\<exists>\<tau>. (v, \<tau>) \<in> \<Gamma>)"
  apply (induction rule:has_type.induct, auto)
  by metis+

corollary well_typed_no_fvs:
  "[] \<turnstile> e : \<tau> \<Longrightarrow> fvs e = {}"
  (* sledgehammer *)
  by (meson ex_in_conv has_type_in_ctx.simps(1) well_typed_fvs)

lemma subst_preservation:
  "\<lbrakk> ((x, \<tau>')#\<Gamma>) \<turnstile> e2 : \<tau>; [] \<turnstile> e1 : \<tau>' \<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile> subst x e1 e2 : \<tau>"
proof (induct e2 arbitrary: \<Gamma> \<tau> \<tau>' x)
  case (Var v)
  then show ?case
    (* found by sledgehammer *)
    by (metis TypeVar TypeVarE context_strengthening has_type_in_ctx.simps(1) has_type_in_ctx.simps(2) subst.simps(2))
next
  case (Abs y \<sigma> e)
  then show ?case
  proof (cases "x = y")
    case False
    with Abs(2) obtain \<tau>\<^sub>2 where "\<tau> = (\<sigma> \<rightarrow> \<tau>\<^sub>2)" "((y, \<sigma>)#(x, \<tau>')#\<Gamma>) \<turnstile> e : \<tau>\<^sub>2"
      by (induct "(x, \<tau>') # \<Gamma>" "Abs y \<sigma> e" "\<tau>" rule:has_type.induct, blast)
    then have "((x, \<tau>')#(y, \<sigma>)#\<Gamma>) \<turnstile> e : \<tau>\<^sub>2"
      (* found by sledgehammer *)
      using False context_strengthening has_type_in_ctx.simps(2) by presburger
    then show ?thesis
      (* found by sledgehammer *)
      by (simp add: Abs.hyps Abs.prems(2) False \<open>\<tau> = \<sigma> \<rightarrow> \<tau>\<^sub>2\<close>)
  qed (auto simp: context_strengthening)
qed fastforce+

theorem preservation:
  "reduce e e' \<Longrightarrow> [] \<turnstile> e : \<tau> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
proof (induct arbitrary: \<tau> rule:reduce.induct)
  case (RApp e2 x \<tau>' e)
  from RApp.prems show ?case
    by (induct "[] :: ctx" "App (Abs x \<tau>' e) e2" "\<tau>")
       (* found by sledgehammer *)
       (metis expr.inject(2) expr.simps(11) expr.simps(15) expr.simps(7) has_type.simps subst_preservation type.inject)
qed blast+



end