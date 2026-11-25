---
title: "The longest sign run of Keiper-Li second differences: a torus problem and its dual"
author: "Michaël Perreault"
date: "2026-11-24"
format: "article"
toc: false
header_footer_policy: "all"
footer: "© 2026 Michaël Perreault · CC BY 4.0"
pageof: true
date_footer: "YYYY-MM-DD"
header_title: "Longest sign run of Keiper-Li second differences"
header-includes:
  - \usetikzlibrary{arrows.meta}
  - \renewcommand{\thetheorem}{T\arabic{theorem}}
  - \newcommand{\Lstr}{L^{*}_{\mathrm{strict}}}
  - \newcommand{\Lclo}{L^{*}_{\mathrm{closed}}}
  - \newcommand{\Lrh}{L_{\mathrm{RH}}}
---

**Abstract.** Let $c_n=\lambda_{n+1}-2\lambda_n+\lambda_{n-1}$ be the second differences of the Li coefficients. Under the Riemann hypothesis (RH), every run of one sign of $c_n$ has length at most $593$, improving the bound $621$ of a previous paper by the author (certified, conditional on RH). The companion torus problem, in which the phases $n\theta_k$ of the cosines in the zero formula for $c_n$ are replaced by free phases, has value between $589$ and $593$: the upper bound is conditional on RH and uses a certified list of $2000$ zeros, and the lower bound is conditional on RH and on a trusted zero count for the first $1400$ zeros (certified, conditional). Under RH and the independence of $\pi$ and the zero angles over $\mathbb{Q}$ (hypothesis $\mathrm{LI}_\theta$), the torus value equals the longest run of $c_n$ (proved), so the bracket is two-sided for $c_n$ only then. A duality theorem identifies the best weights that depend on the phase of the first zero with a relaxation of the torus problem, and shows that a finite certificate exists exactly above the torus value (proved). Under RH, the trusted zero count and $\mathrm{LI}_\theta$ for the zeros up to height $2\cdot10^5$, runs of $589$ values of each sign occur with positive lower density, using an explicit zero-counting bound of Bellotti and Wong (conditional). The method of the previous paper, which gave runs of $476$ under independence of the first $1400$ angles, cannot give a window of $534$ or more, for any number of listed zeros up to $2000$ (certified).

```{=latex}
\begingroup\small
This work is licensed under the Creative Commons Attribution 4.0 International License (CC BY 4.0), https://creativecommons.org/licenses/by/4.0/. The accompanying code is MIT-licensed.
\par\endgroup
```

# Introduction

Let $\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and let $\lambda_n$ be the Li coefficients, defined by $\log\bigl(2\xi\bigl(\tfrac{1}{1-z}\bigr)\bigr)=\sum_{n\ge1}\lambda_n z^n/n$, with $\lambda_0=0$. Put
$$
c_n=\lambda_{n+1}-2\lambda_n+\lambda_{n-1}\qquad(n\ge1),
$$
Keiper's sequence $\tau_n$ [1]. A *run* is a maximal block of consecutive indices $n\ge1$ with $c_n$ of one strict sign. In the earlier paper [2] we proved, assuming RH, that every run has length at most $621$ (its Theorem A); that runs of $312$ values of each sign recur (Theorem B); and, assuming RH and a linear independence hypothesis on the first $700$ or $1400$ zero angles, that runs of $392$ and $476$ recur (Theorem C). The true longest run was left open between $312$ and $621$ under RH, and between $476$ and $621$ under the independence hypothesis. This paper narrows both ends, for a precisely defined companion problem.

**The idea.** Under RH, $c_n=\sum_{\gamma}2m_\gamma w_\gamma\cos(n\theta_\gamma)$ [2, zero formula], a sum over the zeros $\tfrac12+i\gamma$ with angles $\theta_\gamma=2\arctan\frac1{2\gamma}$. A run of $L$ positive values is a window of $L$ indices on which this sum stays positive. If we replace the phases $n\theta_\gamma$ by arbitrary phases $x_\gamma$, we get a sum $F_x$ on an infinite torus. Every run of $c_n$ is a window of $F_x$ at the point $x=(n\theta_\gamma)_\gamma$, so the longest run of $c_n$ is at most the longest window of $F_x$ over the torus; and when the angles are independent over $\mathbb{Q}$, Weyl's theorem [14] makes the two equal. The torus problem is a clean extremal problem with a primal side (find phases that make a long positive window) and a dual side (find weights that prove no such window exists). We bound it from both sides with certificates, and we prove the duality that relates the two.

**Zeros and angles.** Assume RH. Write the distinct ordinates of the zeros with $\gamma>0$ as $\gamma_1<\gamma_2<\cdots$, with multiplicities $m_k$, and put
$$
\theta_k=2\arctan\frac1{2\gamma_k},\quad w_k=\frac1{\tfrac14+\gamma_k^2},\quad a_k=2m_kw_k,\quad C=\sum_k a_k=2\lambda_1=2+\gamma_E-\log4\pi\approx0.0461914 .
$$
For $K\ge0$ the *tail mass* is $T_K=\sum_{k>K}a_k=C-\sum_{k\le K}a_k>0$.

**Hypotheses.** We use the following.

- **RH.** Every nontrivial zero of $\zeta$ has real part $\tfrac12$.
- **$\mathrm{LI}_\theta$.** The numbers $\pi,\theta_1,\theta_2,\dots$ (distinct angles, each once) are linearly independent over $\mathbb{Q}$. Multiplicity then only scales the amplitudes $a_k$. This is implied by the hypothesis of the same name in [2], which counts multiplicities and so also forces simple zeros.
- **$\mathrm{LI}_\theta(\Gamma)$.** The same for $\pi$ and the angles of the zeros with $0<\gamma\le\Gamma$.

The bare phrase "linear independence" is never used below without one of these names; none of them is known.

**Labels.** *Proved* means an argument written in this paper. *Certified* means a finite inequality verified in ball arithmetic with Arb [3] from archived exact inputs (certificates C1 to C4, Appendix B; C5 is a cross-check, not a certificate; C6 is a second check of C2 in exact rational arithmetic); every certified result also carries its hypotheses, which a certificate does not remove. A result may carry two labels, for example certified and conditional on part (b) of the zero list (Section 2). *Conditional* means that a hypothesis in the table is used. *Numerical* means floating point, not a certificate; every number in this paper that is not proved or certified is marked numerical.

**Results.** Section 2 defines the torus problem. We write $\Lstr$ and $\Lclo$ for the longest window on which $F_x>0$, respectively $F_x\ge0$, over the whole torus, and $\Lrh$ for the longest run of $c_n$.

| Result | Statement | Hypotheses | Label |
|-----|--------------------------------------|----------------|-----------|
| T1 | $\Lrh\le\Lstr\le\Lclo$; $\Lstr$ lies between three finite problems in which the unlisted zeros are adversarial, favourable or aligned (Section 2); $\Lrh=\Lstr$ | RH; for the equality also $\mathrm{LI}_\theta$ | proved |
| T2 | duality (Section 3): fixed weights certify nothing; the best weights that depend on the first phase match a relaxation of the torus problem; a finite certificate exists exactly above $\Lclo$ | none beyond the model | proved |
| T3 | $\Lstr\ge589$, so no argument that treats the phases as unknown proves a bound of $588$ | RH; part (b) of the zero list (Arb's zero count, trusted) | certified (C1), conditional |
| T4 | every window of $594$ consecutive indices has both signs; runs have length at most $593$ | RH | certified (C2), conditional |
| T5 | $589\le\Lstr\le\Lclo\le593$; for $c_n$: $\Lrh\le593$, and $589\le\Lrh$ only with $\mathrm{LI}_\theta$ | RH and part (b) for the lower half; RH for the upper half; for $c_n$ also $\mathrm{LI}_\theta$ | certified (C1, C2), conditional |
| T6 | runs of $589$ values of each sign, of positive lower density | RH; part (b); $\mathrm{LI}_\theta(2\cdot10^5)$ | conditional, tail certified (C4) |
| T7 | the robust-tail problem (the method of Theorem C of [2]; the unlisted zeros are adversarial) has no window of $534$ for $K\le2000$ (Section 6) | none for the $K$-zero model; RH and part (b) for the true zeros | certified (C3) |

Here T4 improves Theorem A of [2] from $622$ to $594$ with the same hypothesis. The lower bound in T3 and T5 is a statement about $F_x$ on the torus; for the sequence $c_n$ it is a lower bound only under $\mathrm{LI}_\theta$, because RH alone does not say that the phases $n\theta_k$ come near the point we use.

**What is new, and what is not.** To our knowledge, the bracket T5, the number $593$, the duality T2 in the form stated, and T7 are new. The weak duality behind T2 and the comb of weights are classical in mechanism. Haraux [5] proves the continuous-time analogue of bounded run length for almost periodic functions of mean zero, and Kozma and Oravecz [6] use an iterated two-point averaging comb for such problems, the method closest to ours. Logan's problems on eventually one-signed positive definite bandlimited functions, as stated by Gorbachev, Ivanov and Tikhonov [7], are a continuous cousin. Gilbert and Smyth [8] determine, for integer frequencies $1,\dots,n$ and free coefficients, the longest interval on which a zero-mean cosine polynomial is nonnegative; this does not cover fixed real frequencies and fixed amplitudes. The reduction from independence to the torus is the Kronecker-Weyl route of Rubinstein and Sarnak [9]. For [8], [9] and Logan's papers we rely on the accounts cited ([7], [10]); we prove the step we need directly. The convex analysis in T2 is textbook [4, §2.5.1, §4.4.2, §5.2.3]; we claim only the formulation. For rigour by interval arithmetic after a floating-point optimisation there is a precedent in Chirre, Gonçalves and de Laat [11], on a different problem.

**Remark (Alpöge).** On 20 November 2026 Alpöge [12] announced a proof of the Riemann hypothesis, together with a Lean 4 formalization. The Lean FRO and Mathlib Initiative [13] report that the formal proof was checked by the Lean kernel and by independent third-party checkers. As of 24 November 2026 we found no human-readable proof, and the announcement has not been peer reviewed. If the proof is accepted, T1 to T5 hold without assuming RH. T6 would still need $\mathrm{LI}_\theta(2\cdot10^5)$, which the announced result does not supply, and so would the equality in T1 and the two-sided reading of T5 for $c_n$.

**Outline.** Section 2 defines the torus problem and proves T1. Section 3 proves the duality T2. Section 4 states the alignment lemma and proves T3 from certificate C1. Section 5 proves T4 and T5, Section 6 proves T6 and T7, Section 7 gives the numerical evidence and Section 8 open questions. Appendix A states each certificate inequality and Appendix B the reproduction.

# The torus problem

**The zero formula and the zero list.** We use two facts from [2] and restate them. *Zero formula* [2]: assume RH; then for $n\ge1$
$$
c_n=\sum_{k\ge1}a_k\cos(n\theta_k),\qquad \sum_k a_k=C,
$$
the series converging absolutely. *Zero list* [2, Lemma on the zero list]: with $T=2638142521/2^{20}\approx2515.93$ and stored midpoints $\mu_1<\dots<\mu_{2000}$, (a) Hardy's function $Z$ has opposite signs at $\mu_k\pm2^{-20}$, so the pairwise disjoint intervals $I_k=[\mu_k-2^{-20},\mu_k+2^{-20}]$ each contain an ordinate of odd multiplicity; (b) there are exactly $2000$ zeros with $0<\gamma\le T$, all simple and on the line, and $\gamma_k\in I_k$. Part (b) rests on Arb's count of zeros being correct, which we trust and do not certify. Every use of part (b) below is marked.

**The torus and the sum $F_x$.** Let $\mathbb{T}=\mathbb{R}/2\pi\mathbb{Z}$ and $\mathbb{T}^\infty=\mathbb{T}^{\mathbb{N}}$ with the product topology; it is compact. For $x\in\mathbb{T}^\infty$ and integer $j$ put
$$
F_x(j)=\sum_{k\ge1}a_k\cos(j\theta_k+x_k),\qquad F^K_x(j)=\sum_{k\le K}a_k\cos(j\theta_k+x_k).
$$
The series converges uniformly because $\sum a_k=C<\infty$, so $x\mapsto F_x(j)$ is continuous, and $|F_x(j)-F^K_x(j)|\le T_K$ for all $x$ and $j$. Two symmetries are used. First, $F_{x+\pi}=-F_x$ (add $\pi$ to every coordinate), so negative windows are positive windows at another point. Second, for $x'_k=-x_k-(L-1)\theta_k$ we have $F_{x'}(L-1-j)=F_x(j)$, the reflection of a window of length $L$ about its centre. Shifting the window, $j\mapsto j+s$, changes $x_k$ to $x_k+s\theta_k$, so we may always take windows to be $j=0,\dots,L-1$.

**Window lengths.** For $x\in\mathbb{T}^\infty$ let $\ell_>(x)\in\{0,1,\dots,\infty\}$ be the largest $L$ with $F_x(j)>0$ for $0\le j<L$, and $\ell_\ge(x)$ the same with $F_x(j)\ge0$. Put
$$
\Lstr=\sup_x\ell_>(x),\qquad \Lclo=\sup_x\ell_\ge(x),\qquad\text{so }\Lstr\le\Lclo .
$$
Let $\Lrh$ be the length of the longest run of $c_n$, of either sign (a run is a block of strict sign, as in the Introduction). Fix $K$ and $L$ and put $\kappa=(L-1)/2$. We use three finite problems, each the largest $L$ for which some $x\in\mathbb{T}^K$ satisfies, for all $0\le j<L$:

- **robust tail**, $L_c(K)$: $F^K_x(j)>T_K$;
- **aligned tail**, $L_a(K)$: $F^K_x(j)>-T_K\cos\bigl(\min(|j-\kappa|\,\theta_K,\pi)\bigr)$;
- **favourable tail**, $L_f(K)$: $F^K_x(j)>-T_K$.

In the robust problem the unlisted zeros are adversarial at every $j$; in the favourable problem they may take any value in $[-T_K,T_K]$; in the aligned problem they are placed at a crest at the window centre, the best a single common phase choice can do. The aligned condition without the minimum is the one used in practice, since $(L-1)\theta_K\le2\pi$ for every window below.

```{=latex}
\begin{theorem}[sandwich and reduction]\label{thm:T1}
```
Assume RH. Then:

(a) $L_c(K)\le L_a(K)\le\Lstr\le\Lclo$ and $\Lstr\le L_f(K)$, for every $K$. The function $L_c$ is nondecreasing and $L_f$ is nonincreasing in $K$. If $\Lstr<\infty$, then $L_c(K)=\Lstr$ for all large $K$ (and in general $L_c(K)\to\Lstr$). If $\Lclo<\infty$, then $\Lstr\le L_f(K)\le\Lclo$ for all large $K$.

(b) $\Lrh\le\Lstr\le\Lclo$.

(c) If also $\mathrm{LI}_\theta$ holds, then $\Lrh=\Lstr$, and every strict window of $F_x$ occurs in $c_n$ with positive lower density.

```{=latex}
\end{theorem}
```

<!-- statement
id: T1
label: PROVED
-->

**Hypotheses:** RH throughout (it defines $F_x$ through the zero formula; T1(a) is a statement about the model only); $\mathrm{LI}_\theta$ for the equality in T1(c). The finiteness assumptions in T1(a) hold by T5 below ($\Lclo\le593$ under RH and zero-list part (a)), or by Theorem A of [2]; without them the corresponding clause is vacuous. The inequality $\Lclo\le L_f(K)$ is not claimed: a closed window gives only $F^K\ge-T_K$. Part (c) is the only place where independence enters.

```{=latex}
\begin{proof}
```
(a) *Aligned tail below $\Lstr$.* Let $x\in\mathbb{T}^K$ satisfy the aligned condition on $0\le j<L$. Extend it by $x_k=-\kappa\theta_k$ for $k>K$. For $k>K$ we have $0<\theta_k<\theta_K$, so $0\le|j-\kappa|\theta_k\le|j-\kappa|\theta_K$; as $\cos$ is decreasing on $[0,\pi]$, $\cos((j-\kappa)\theta_k)\ge\cos(\min(|j-\kappa|\theta_K,\pi))$. Multiplying by $a_k$ and summing over $k>K$ gives that the tail of $F_x(j)$ is at least $T_K\cos(\min(|j-\kappa|\theta_K,\pi))$. Hence $F_x(j)=F^K_x(j)+\text{tail}>0$, and $L_a(K)\le\Lstr$.

*Robust below aligned.* If $F^K_x(j)>T_K$ then $F^K_x(j)>T_K\ge-T_K\cos(\cdot)$, since $-\cos\le1$. So $L_c(K)\le L_a(K)$.

*Torus below favourable.* If $F_x(j)>0$ on the window then $F^K_x(j)=F_x(j)-\text{tail}>-T_K$, so the restriction of $x$ to $\mathbb{T}^K$ is admissible for $L_f(K)$.

*Monotonicity.* Since $T_{K+1}=T_K-a_{K+1}$: if $F^K_x>T_K$ on a window, then for any choice of $x_{K+1}$, $F^{K+1}_x-T_{K+1}=F^K_x+a_{K+1}\cos(\cdot)-T_K+a_{K+1}\ge F^K_x-T_K>0$, so $L_c(K+1)\ge L_c(K)$. If $F^{K+1}_x>-T_{K+1}$ on a window then $F^K_x\ge F^{K+1}_x-a_{K+1}>-T_{K+1}-a_{K+1}=-T_K$, so $L_f(K)\ge L_f(K+1)$.

*Limits.* Let $L\le\Lstr$ be an integer and $x$ a point with $F_x>0$ on $0\le j<L$; the minimum $m$ of the finitely many values is positive. Choose $K$ with $2T_K<m$. Then $F^K_x(j)\ge F_x(j)-T_K\ge m-T_K>T_K$, so $L_c(K)\ge L$; by monotonicity this holds for all larger $K$. Hence $L_c(K)\to\Lstr$, and if $\Lstr<\infty$ the nondecreasing integer sequence $L_c(K)\le\Lstr$ equals $\Lstr$ from some $K$ on. Now let $\Lclo<\infty$ and $L=\Lclo+1$. No $x$ has $F_x\ge0$ on the window, so the continuous function $x\mapsto\min_{j<L}F_x(j)$ on the compact space $\mathbb{T}^\infty$ has a maximum $-\eta<0$. Take $K$ with $2T_K<\eta$. If some $y\in\mathbb{T}^K$ had $F^K_y>-T_K$ on the window, extend it arbitrarily to $x\in\mathbb{T}^\infty$; then $F_x(j)\ge F^K_y(j)-T_K>-2T_K>-\eta$ for all $j<L$, contradicting the maximum. So $L_f(K)\le\Lclo$ for this $K$ and, by monotonicity, all larger $K$. Together with $\Lstr\le L_f(K)$ this gives the last claim of (a).

(b) Let $c_n,\dots,c_{n+L-1}$ be a run of positive values. Put $x_k=n\theta_k$ (mod $2\pi$). By the zero formula, $F_x(j)=c_{n+j}>0$ for $0\le j<L$, so $\ell_>(x)\ge L$. For a run of negative values take $x_k=n\theta_k+\pi$ and use $F_{x+\pi}=-F_x$. Hence $\Lrh\le\Lstr$.

(c) Let $L\le\Lstr$ be an integer and $x$ with $F_x>0$ on $0\le j<L$, with minimum $m>0$ as above. Choose $K$ with $2T_K<m/2$ and $\delta>0$ with $\delta C<m/4$. Under $\mathrm{LI}_\theta$ the numbers $1,\theta_1/2\pi,\dots,\theta_K/2\pi$ are linearly independent over $\mathbb{Q}$, so by Weyl's theorem [14] the sequence $(n\theta_1,\dots,n\theta_K)$ is equidistributed in $\mathbb{T}^K$; the set $\mathcal{N}$ of $n\ge1$ with $|n\theta_k-x_k|<\delta$ (in $\mathbb{T}$) for all $k\le K$ therefore has positive lower density. For $n\in \mathcal{N}$, $|\cos((n+j)\theta_k)-\cos(j\theta_k+x_k)|\le|n\theta_k-x_k|<\delta$, so
$$
c_{n+j}\ge F^K_x(j)-\delta\sum_{k\le K}a_k-T_K\ge(m-T_K)-\delta C-T_K>m-\tfrac m4-\tfrac m2>0\qquad(0\le j<L),
$$
using $F^K_x\ge m-T_K$ and the tail bound $T_K$ of the zero formula. So $c_{n},\dots,c_{n+L-1}$ is a window of positive values, contained in a run of length at least $L$. Hence $\Lrh\ge L$ for every $L\le\Lstr$, and with (b), $\Lrh=\Lstr$.
```{=latex}
\end{proof}
```

**Phase-uniform arguments.** A *phase-uniform argument* for the bound $L$ is a proof that $\ell_\ge(x)<L$ for every $x\in\mathbb{T}^\infty$, for the true amplitudes $a_k$ and angles $\theta_k$. Theorem A of [2] and Theorem T4 below are of this form. By definition such an argument can never prove a bound below $\Lclo+1$; Section 3 shows it can reach that value in principle. Under RH alone we know nothing about which points of $\mathbb{T}^\infty$ the phases $(n\theta_k)_k$ approach, which is why the torus problem, and not $c_n$, is the object of the lower bound.

# Duality

**Weights and certificates.** Fix $K$, a number $W\ge T_K$ (a *tail allowance*) and $L$. A *weight vector* is $\beta=(\beta_0,\dots,\beta_{L-1})$ with $\beta_j\ge0$ and $\sum_j\beta_j=1$; put $B_\beta(\theta)=\sum_j\beta_je^{ij\theta}$ and, for $x_1\in\mathbb{T}$,
$$
G(\beta;x_1)=a_1\,\mathrm{Re}\bigl(e^{ix_1}B_\beta(\theta_1)\bigr)+\sum_{k=2}^{K}a_k\,|B_\beta(\theta_k)|+W .
$$
A *conditioned certificate* of type $(K,W,L)$ is a finite list of open arcs $A_i\subset\mathbb{T}$ covering $\mathbb{T}$, each with a weight vector $\beta^{(i)}$, such that $G(\beta^{(i)};x_1)<0$ for every $x_1\in A_i$. The weights depend on the phase $x_1$ of the first zero only through the arc.

*Weak duality.* If a conditioned certificate of type $(K,W,L)$ exists, then no $x\in\mathbb{T}^\infty$ has $F_x\ge0$ on a window of length $L$. Indeed, for $x_1\in A_i$ and any $x_2,\dots,x_K$, $\sum_j\beta_j^{(i)}F^K_x(j)\le G(\beta^{(i)};x_1)-W$, because $\mathrm{Re}(e^{ix_k}B_\beta(\theta_k))\le|B_\beta(\theta_k)|$. If $F_x\ge0$ on the window then $F^K_x(j)\ge-T_K\ge-W$, so $\sum_j\beta^{(i)}_j(F^K_x(j)+W)\ge0$ since $\beta\ge0$, while the left side is at most $G<0$, a contradiction. The comb of [2] is the special case where $\beta$ is supported on $M$ indices spaced about $2\pi/\theta_1$ apart, at the troughs of the first zero.

**The disc relaxation.** For $K$, $W$ and $L$ the *disc relaxation* is the set of $(x_1,z_2,\dots,z_K)$ with $x_1\in\mathbb{T}$ and $z_k\in\mathbb{C}$, $|z_k|\le1$, together with the window values
$$
F^\Delta(j)=a_1\cos(j\theta_1+x_1)+\sum_{k=2}^{K}a_k\,\mathrm{Re}\bigl(z_ke^{ij\theta_k}\bigr).
$$
It *has a run of length $L$* if some point satisfies $F^\Delta(j)+W\ge0$ for $0\le j<L$. The first zero keeps full amplitude, the others may be damped; with $|z_k|=1$ for all $k$ we recover the torus values $F^K_x$. Let $D(K,W)$ be the largest $L$ for which the relaxation has a run. Every point $x\in\mathbb{T}^K$ with $F^K_x\ge-W$ on a window is a point of the relaxation, so $\Lclo\le D(K,W)$ for every $K$ and every $W\ge T_K$.

```{=latex}
\begin{theorem}[duality]\label{thm:T2}
```
Assume RH and use the notation above.

(a) *Fixed weights fail.* For every weight vector $\beta$ and every $K$, $\max_{x\in\mathbb{T}^K}\sum_j\beta_j\bigl(F^K_x(j)+W\bigr)\ge W>0$. So no single weight vector certifies any window.

(b) *Best conditioned weights.* For fixed $x_1$, minimising $G(\beta;x_1)$ over weight vectors is a second-order cone program, and its value is negative if and only if the disc relaxation has no point with first phase $x_1$ and a run of length $L$. A conditioned certificate of type $(K,W,L)$ exists if and only if the disc relaxation has no run of length $L$, that is, if and only if $L>D(K,W)$.

(c) *The limit of phase-uniform methods.* Suppose $\Lclo<\infty$. For every $L>\Lclo$ there is a finite certificate of the following kind: a number $K$, a finite cover of $\mathbb{T}^K$ by boxes, and for each box an index $j<L$ with $F^K_x(j)+T_K<0$ for all $x$ in the box. Such a certificate shows that no $x\in\mathbb{T}^\infty$ has $F_x\ge0$ on a window of length $L$. No finite phase-uniform certificate, of any kind, exists for $L\le\Lclo$.

```{=latex}
\end{theorem}
```

<!-- statement
id: T2
label: PROVED
-->

**Hypotheses:** the model of Section 2 only (RH to define $F$; none of the zero list). The hypothesis $\Lclo<\infty$ in (c) holds by T5 (RH and part (a)) or by Theorem A of [2]; otherwise (c) is vacuous. In (c), "certificate" means a finite object whose validity implies that every $x\in\mathbb{T}^\infty$ has some $j<L$ with $F_x(j)<0$, that is, a proof of $\Lclo<L$; a certificate that excludes only strict windows could exist down to $\Lstr+1$, and we make no claim about it. The convex analysis is standard [4]; what is stated is the identification of the best conditioned weights with the disc relaxation.

```{=latex}
\begin{proof}
```
(a) Let $\beta$ be a weight vector. Averaging over $x\in\mathbb{T}^K$ with Haar measure, each $\cos(j\theta_k+x_k)$ has mean $0$, so the mean of $\sum_j\beta_j(F^K_x(j)+W)$ is $W\sum_j\beta_j=W$. A function on $\mathbb{T}^K$ attains a maximum at least its mean.

(b) *The set $V(x_1)$.* Fix $x_1$ and put $v_j(z)=a_1\cos(j\theta_1+x_1)+\sum_{k=2}^Ka_k\mathrm{Re}(z_ke^{ij\theta_k})+W$ for $z=(z_2,\dots,z_K)$ in the product $\Delta$ of closed unit discs. The map $z\mapsto(v_j(z))_{j<L}\in\mathbb{R}^L$ is affine in $z$ (the real-linear map $z_k\mapsto(\mathrm{Re}(z_ke^{ij\theta_k}))_j$ plus a constant), so its image $V(x_1)$ is compact and convex, a point plus a Minkowski sum of linear images of discs. Let $O=\{v\in\mathbb{R}^L:v_j\ge0\ \forall j\}$. By definition the relaxation has a run of length $L$ with first phase $x_1$ if and only if $V(x_1)\cap O\ne\emptyset$.

*The support function.* For $\beta\ge0$, $\max_{v\in V(x_1)}\beta\cdot v=G(\beta;x_1)$. Indeed $\beta\cdot v(z)=a_1\mathrm{Re}(e^{ix_1}B_\beta(\theta_1))+\sum_ka_k\mathrm{Re}(z_kB_\beta(\theta_k))+W\sum\beta_j$, a sum of terms each maximised over $|z_k|\le1$ at $z_k=\overline{B_\beta(\theta_k)}/|B_\beta(\theta_k)|$ (any $z_k$ if $B=0$), with value $a_k|B_\beta(\theta_k)|$, and $\sum\beta_j=1$. Since $G$ is convex in $\beta$ (each $|B_\beta(\theta_k)|$ is a Euclidean norm of a linear function of $\beta$ and the first term is linear), minimising $G(\cdot;x_1)$ over the simplex is a second-order cone program: minimise $a_1\mathrm{Re}(e^{ix_1}B_\beta(\theta_1))+\sum_{k\ge2}a_ks_k+W$ subject to $s_k\ge\|(\mathrm{Re}\,B_\beta(\theta_k),\mathrm{Im}\,B_\beta(\theta_k))\|$, $\beta\ge0$, $\sum\beta_j=1$ [4, §4.4.2].

*Pointwise equivalence.* If $\beta$ is a weight vector with $G(\beta;x_1)<0$ then every $v\in V(x_1)$ has $\beta\cdot v<0$, while every $v\in O$ has $\beta\cdot v\ge0$; so $V(x_1)\cap O=\emptyset$. Conversely let $V(x_1)\cap O=\emptyset$. As $V(x_1)$ is compact and $O$ closed, their distance is some $\delta>0$, and $V_\delta=V(x_1)+\{u:\|u\|\le\delta/2\}$ is compact, convex and disjoint from $O$. By the separating hyperplane theorem [4, §2.5.1] there are $\alpha\ne0$ and $b$ with $\alpha\cdot v\le b\le\alpha\cdot u$ for $v\in V_\delta$, $u\in O$. Since $O$ is a cone, $\alpha\cdot u\ge b$ on $O$ forces $\alpha\ge0$ (test $u=te_j$, $t\to\infty$) and $b\le0$ (test $u=0$). Since $V_\delta$ contains $v+\tfrac\delta2\alpha/\|\alpha\|$ for each $v\in V(x_1)$, we get $\max_{V(x_1)}\alpha\cdot v+\tfrac\delta2\|\alpha\|\le b\le0$, so, with $\beta=\alpha/\sum_j\alpha_j$, $G(\beta;x_1)=\max_{V(x_1)}\beta\cdot v<0$. This proves the statement about the cone program.

*From points to a finite certificate.* If the relaxation has no run of length $L$, then for every $x_1\in\mathbb{T}$ there is $\beta$ with $G(\beta;x_1)<0$. For fixed $\beta$ the function $x_1\mapsto G(\beta;x_1)$ is continuous, so $G(\beta;\cdot)<0$ on an open arc around $x_1$. By compactness of $\mathbb{T}$ finitely many such arcs cover $\mathbb{T}$; this is a conditioned certificate. Conversely, given a conditioned certificate and any $x_1\in\mathbb{T}$, pick $i$ with $x_1\in A_i$; then $G(\beta^{(i)};x_1)<0$, so $V(x_1)\cap O=\emptyset$. Hence there is no run of length $L$ at any $x_1$. The lengths with a run are exactly $L\le D(K,W)$, since a run of length $L$ contains a run of every smaller length.

(c) *Existence above $\Lclo$.* Let $L>\Lclo$ be an integer. No $x\in\mathbb{T}^\infty$ has $F_x\ge0$ on $0\le j<L$, so the continuous function $x\mapsto\min_{j<L}F_x(j)$ on the compact space $\mathbb{T}^\infty$ has a maximum $-\eta<0$: for every $x$ some $j<L$ has $F_x(j)\le-\eta$. Choose $K$ with $T_K<\eta/8$ and a mesh $h>0$ with $Ch<\eta/4$. Cover $\mathbb{T}^K$ by finitely many boxes of sup-norm half-width $h$ with centres $y$. For a centre $y$, extend it by zeros to $x\in\mathbb{T}^\infty$ and choose $j<L$ with $F_x(j)\le-\eta$; then $F^K_y(j)\le F_x(j)+T_K\le-\eta+T_K$. For any point $x'$ of the box, $|F^K_{x'}(j)-F^K_y(j)|\le\sum_ka_k|x'_k-y_k|\le Ch<\eta/4$, so $F^K_{x'}(j)+T_K<-\eta+2T_K+\eta/4<0$. This is the certificate. It excludes closed windows: for any $x\in\mathbb{T}^\infty$ the restriction $x'$ to $\mathbb{T}^K$ lies in a box, and $F_x(j)\le F^K_{x'}(j)+T_K<0$ for the box's index $j<L$.

*Nonexistence at or below $\Lclo$.* Let $1\le L\le\Lclo$ be an integer. By the definition of $\Lclo$ as a supremum of integers there is $x$ with $\ell_\ge(x)\ge L$, that is, $F_x\ge0$ on $0\le j<L$; a certificate would assert that some $j<L$ has $F_x(j)<0$ for this $x$.
```{=latex}
\end{proof}
```

**Consequences and limits of the statement.** By (b) and the inequality $\Lclo\le D(K,W)$, the best certificate whose weights depend only on the phase of the first zero, for $K$ listed zeros and allowance $W=T_K$, proves exactly the bound $D(K,T_K)$ and nothing smaller; the obstruction is that the relaxation allows a listed zero to be damped to modulus $|z_k|<1$, which the dual cannot distinguish from full amplitude. We do not claim $D(K,T_K)\to\Lclo$ as $K\to\infty$. Part (c) says the limit of all phase-uniform methods is $\Lclo$, at a cost that grows with $K$ and the mesh. Weights that depend on more phases, or a semidefinite relaxation in place of the discs, are the obvious ways to shrink the gap; we do not pursue them here.

**Remark (why per-shift weights do not help).** If the comb of [2] were placed at real times, shifting the window would multiply each $B_\beta(\theta_k)$, $k\ge2$, by a unit complex number, so $G$ would not depend on the shift and weights chosen per shift would equal one uniform vector (proved for real shifts). On the integers the rounding of the window position changes $G$ only at first order in $\theta_1/2$; we expect a gain of a fraction of a percent at most (heuristic). Any larger gain must come from the shape of the weights over the whole window, which is what certificate C2 of Section 5 uses.

# The lower side

**The alignment lemma.** The tail of $F_x$ cannot be made large by independent choices at every $j$, but the zeros above $\gamma_K$ have long periods compared with the window, so one common phase choice almost achieves the favourable value.

```{=latex}
\begin{lemma}[alignment]\label{lem:align}
```
Let $K\ge0$, let $L\ge1$ and $\kappa=(L-1)/2$, and let $\bar\theta>0$ satisfy $\theta_k\le\bar\theta$ for all $k>K$ and $(L-1)\bar\theta\le2\pi$. For $x_k=-\kappa\theta_k$ ($k>K$) and every $0\le j<L$,
$$
\sum_{k>K}a_k\cos(j\theta_k+x_k)\ \ge\ T_K\cos\bigl(|j-\kappa|\,\bar\theta\bigr)\ \ge\ T_K\cos\!\bigl(\tfrac{(L-1)\bar\theta}{2}\bigr)\ \ge -T_K .
$$
Hence if $x\in\mathbb{T}^\infty$ extends $y\in\mathbb{T}^K$ by these phases, then $F_x(j)\ge F^K_y(j)+T_K\cos(|j-\kappa|\bar\theta)$.

```{=latex}
\end{lemma}
```

<!-- statement
id: L3
label: PROVED
-->

```{=latex}
\begin{proof}
```
For $k>K$, $\cos(j\theta_k+x_k)=\cos((j-\kappa)\theta_k)$ and $0\le|j-\kappa|\theta_k\le|j-\kappa|\bar\theta\le(L-1)\bar\theta/2\le\pi$; cosine is decreasing on $[0,\pi]$, so each term is at least $a_k\cos(|j-\kappa|\bar\theta)$. Sum over $k>K$.
```{=latex}
\end{proof}
```

Under the zero list part (b) of Section 2, every zero beyond the first $1400$ has ordinate larger than the lower end of $I_{1401}$, so $\bar\theta=\theta_{\mathrm{up}}$, the angle of that lower end, is a valid bound for $K=1400$. Here $(L-1)\bar\theta\le2\pi$ holds by a wide margin for $L=589$, since $\bar\theta<10^{-3}$.

```{=latex}
\begin{theorem}[computer-assisted]\label{thm:T3}
```
Assume RH and part (b) of the zero list. There is a point $x\in\mathbb{T}^\infty$ with $F_x(j)>0$ for $0\le j\le588$. Hence $\Lstr\ge589$ and $\Lclo\ge589$. In particular no phase-uniform argument proves a bound of $588$ for the run length of $F_x$ on the torus.

```{=latex}
\end{theorem}
```

<!-- statement
id: T3
label: CONDITIONAL
certificate: papers/keiper-li-run-torus/code/cert_c1_torus589.json
-->

**Hypotheses:** RH, and part (b) of the zero list (the first $1400$ listed zeros are the first $1400$ ordinates, and they are simple). Independence is not used. The statement is about $F_x$ on the torus, not about $c_n$.

```{=latex}
\begin{proof}
```
*What is certified (C1).* Let $y\in\mathbb{T}^{1400}$ be a vector of phases, stored as exact dyadic rationals (denominator $2^{40}$), and $\kappa=294$. Certificate C1 verifies, in ball arithmetic ($128$ bits, python-flint $0.9.0$ [16]), that for every $0\le j\le588$
$$
F^{1400}_y(j)+T_{1400}^{-}\cos\bigl(|j-\kappa|\,\theta_{\mathrm{up}}\bigr)\ \ge\ 5.472\cdot10^{-5}\ >0,
$$
where $T^{-}_{1400}$ is a certified lower end of $T_{1400}$ (the ball arithmetic encloses $\theta_k$ and $w_k$ over the whole interval $I_k$, as in the zero list) and $\theta_{\mathrm{up}}$ is the angle of the lower end of $I_{1401}$. The smallest margin is at $j=246$ (certified). The cosine factor is positive, so a lower end of $T_{1400}$ is a valid lower bound.

*From the certificate to the theorem.* Extend $y$ by $x_k=-\kappa\theta_k$ for $k>1400$. By the zero list (b) the zeros $\gamma_k$, $k>1400$, are at least the lower end of $I_{1401}$, so $\theta_k\le\theta_{\mathrm{up}}$, and the alignment lemma gives $F_x(j)\ge F^{1400}_y(j)+T_{1400}\cos(|j-\kappa|\theta_{\mathrm{up}})\ge5.472\cdot10^{-5}$ for $0\le j\le588$. Hence $\ell_>(x)\ge589$, so $\Lstr\ge589$, and $\Lclo\ge\Lstr$. A phase-uniform argument for the bound $588$ would show $\ell_\ge(x)<589$ for this $x$, which is false.
```{=latex}
\end{proof}
```

**How the phases were found.** The phases are the output of a floating-point search at $K=1400$ for a long window on which $F^{1400}_y>-T_{1400}$ (the favourable tail). It is not part of the proof. The search first reached a window of $584$; a sequential linear programming push with the aligned tail, started from those phases and raising the window by one at each success, reached $589$ with float margin $5.473\cdot10^{-5}$ (numerical), and the certified margin $5.472\cdot10^{-5}$ is the one that counts. The window $590$ was not reached: the best float margin at $590$ was $-1.1\cdot10^{-5}$ at $K=1400$ and $-6.8\cdot10^{-6}$ at $K=2000$ (numerical). A search at $K=2000$ for the favourable tail reached $552$ with margin $9.7\cdot10^{-4}$ (numerical). We do not claim that $589$ is the true value; Section 7 reports the floating-point evidence.

**Broken inputs.** Certificate C1 is tested on inputs that must fail, and each fails or is refused as stated; the list is in Appendix B. These are behaviours of the certificate script, not statements about $F_x$.

**Why the torus statement, and not $c_n$.** T3 does not say that $c_n$ has a run of $589$ under RH. It says that no proof that treats the phases $n\theta_k$ as unknown can prove less than $589$. For $c_n$ the lower bound needs more: under RH and $\mathrm{LI}_\theta$ equality holds by T1(c), so $589\le\Lrh$. With only the independence of the first $K$ angles the tail is adversarial (robust): for the C1 phases the robust tail gives far less (Section 6), and the $476$ of [2] at $K=1400$ is a different, certified robust window; T7 bounds every robust window at $K\le2000$ by $533$. This is why T6 in Section 6 needs independence up to a height of $2\cdot10^5$.

# The upper side

**The idea.** Section 3 explains why conditioned weights can at best prove the bound $D(K,W)$. Certificate C2 is a conditioned certificate of type $(2000,W,594)$ in the sense of Section 3, with a twist forced by the zero list: we know only that each interval $I_k$ contains a zero (part (a) of the zero list), not that it is the $k$-th zero, and the extra amplitude of a zero of higher multiplicity, as well as all unlisted zeros, goes into the allowance $W$. The weights are not a comb on a few indices: each of $48$ weight vectors is spread over the whole window of $594$ indices, and each is used on one arc of phases of the first listed zero.

**Notation for the listed zeros.** Let $\gamma^*_k\in I_k$ be a zero of odd multiplicity, $k\le2000$ (part (a) of the zero list); the $\gamma^*_k$ are distinct because the $I_k$ are disjoint. Write $\theta^*_k$ and $w^*_k$ for its angle and weight. The amplitude of $\gamma^*_k$ in $F_x$ is at least $2w^*_k$. Put
$$
W=C-2\sum_{k\le2000}w_k^*,\qquad\text{so that}\qquad \Bigl|F_x(j)-\sum_{k\le2000}2w^*_k\cos\bigl(j\theta^*_k+x^*_k\bigr)\Bigr|\le W\quad(x\in\mathbb{T}^\infty,\ j\in\mathbb{Z}),
$$
where $x^*_k$ is the coordinate of $x$ belonging to $\gamma^*_k$. Indeed the difference is a sum of cosines whose amplitudes add up to the total amplitude $C$ minus $\sum_k2w^*_k$. Since $w$ decreases with $\gamma$ and $\gamma^*_k\in I_k$, the ball arithmetic of C2 encloses $\theta^*_k$ and $w^*_k$ by balls over the whole interval $I_k$, and $W\le W_{\mathrm{up}}=8.847\cdot10^{-4}$ (certified upper end; it equals the upper end of $T_{2000}$ computed on the same balls). Let $x_1^*$ be the phase of $\gamma^*_1$.

For a weight vector $\beta=(\beta_0,\dots,\beta_{L-1})$ as in Section 3, but not normalised (scaling changes nothing), put $S=\sum_j\beta_j>0$ and $B(\theta)=B_\beta(\theta)=\sum_j\beta_je^{ij\theta}$, and
$$
H(\beta)=\sum_{k=2}^{2000}2w^*_k\,|B(\theta^*_k)|+W S,\qquad \rho(\beta)=\frac{H(\beta)}{2w^*_1\,|B(\theta^*_1)|}.
$$

```{=latex}
\begin{lemma}[weighted bound]\label{lem:wb}
```
Assume RH and part (a) of the zero list. For every $x\in\mathbb{T}^\infty$ and every weight vector $\beta$ with $L$ entries,
$$
\sum_{j<L}\beta_jF_x(j)\ \le\ 2w^*_1\,\mathrm{Re}\bigl(e^{ix_1^*}B(\theta^*_1)\bigr)+H(\beta)\ =\ -2w^*_1|B(\theta^*_1)|\cos(x^*_1-\phi_0)+H(\beta),
$$
where $\phi_0=-\arg B(\theta^*_1)-\pi$. In particular, if $\rho(\beta)<1$ then the right side is negative for every $x$ with $|x^*_1-\phi_0|<\arccos\rho(\beta)$ (distance on $\mathbb{T}$), and then $F_x(j)<0$ for some $j<L$.
```{=latex}
\end{lemma}
```

<!-- statement
id: L5
label: PROVED
-->

```{=latex}
\begin{proof}
```
By the displayed bound on the listed zeros, $\sum_j\beta_jF_x(j)\le\sum_{k\le2000}2w^*_k\,\mathrm{Re}\bigl(e^{ix^*_k}B(\theta^*_k)\bigr)+W S$, because $\sum_j\beta_j\cos(j\theta+y)=\mathrm{Re}(e^{iy}B(\theta))$ and $\beta\ge0$. Bound $\mathrm{Re}(e^{ix_k^*}B(\theta_k^*))\le|B(\theta_k^*)|$ for $k\ge2$; keep $k=1$. Writing $B(\theta^*_1)=|B(\theta^*_1)|e^{i\arg B}$, $\mathrm{Re}(e^{ix_1^*}B)=|B|\cos(x^*_1+\arg B)=-|B|\cos(x_1^*-\phi_0)$. If $\rho<1$ and $|x_1^*-\phi_0|<\arccos\rho$ then $\cos(x_1^*-\phi_0)>\rho$, and the right side is below $-2w_1^*|B|\rho+H=0$. A nonnegative combination of the numbers $F_x(j)$ that is negative forces one of them to be negative.
```{=latex}
\end{proof}
```

**Certificate C2.** The inputs are the $2000$ stored midpoints (the zero list of [2], Section 2) and $48$ weight vectors with $594$ entries each, $\beta_j\in\mathbb{Z}/2^{50}$ (the stored integers are rounded down from a floating-point linear program; the vector with index $i$ was computed for phase $2\pi i/48$ of the first zero; only the integer values matter, how they were found does not). The script (python-flint $0.9.0$, $128$ bits) does the following.

1. It rechecks that Hardy's function $Z$ has strictly opposite signs at both ends of all $2000$ intervals $I_k$ (part (a), certified), and it requires every vector to have exactly $594$ entries.
2. It encloses $\theta^*_k$ and $w^*_k$ by balls over $I_k$ for every $k\le2000$, and $W$ by its upper end $8.847\cdot10^{-4}$. A guard refuses an input allowance $W_{\mathrm{used}}$ below this upper end.
3. For each vector it evaluates $|B(\theta^*_k)|$ by its upper end for $k\ge2$, $|B(\theta^*_1)|$ by its lower end and $\rho$ by its upper end, and requires $\rho<1$.
4. It encloses $\phi_0$ and $\arccos\rho$ in balls and takes the arc $A_i=(\phi_0-\arccos\rho,\ \phi_0+\arccos\rho)$ with the left end replaced by the upper end of the ball and the right end by the lower end, so the computed arc lies inside the true arc for every $\theta^*_1$ in the ball. The arcs and their shifts by $2\pi m$, $m=-1,\dots,2$, are exact rationals.
5. It requires the open arcs to contain every point of $[0,2\pi]$ (using the upper end of $2\pi$); a gap, or two arcs sharing only an endpoint, fails.

No floating-point number enters a decision. The certified outcome (the record of C2, Appendix B):

| quantity | certified value |
|---|---|
| vectors, entries each | $48$, $594$ |
| largest $\rho$ over the vectors | $0.9950736714$ (upper end; $0.99508$) |
| arcs needed | a chain of $22$ arcs covers $[0,2\pi]$ |
| smallest overlap in the chain | $0.01709$ rad |
| tail allowance | $W\le8.847\cdot10^{-4}$ |
| cost | $22$ s on $4$ processes, about $34$ MB per process |

The number $\rho$ is evaluated at the arc centre. The condition that makes the arc valid is $R(\phi)=\rho/\cos(\phi-\phi_0)<1$, and its supremum over the arc is not computed; it is not needed, since the cover only uses the open arcs defined by $R<1$. The overlaps are strict, and $48$ vectors are used where $22$ suffice: removing one or two vectors still passes, removing four consecutive ones leaves a gap (see broken inputs below), so the cover is not tight in the number of vectors. Vectors truncated to $593$ weights fail (one has $\rho\ge1.00054$); this says only that these vectors do not exclude $593$.

```{=latex}
\begin{theorem}[window $594$]\label{thm:T4}
```
Assume RH. Every window of $594$ consecutive indices $n_0\le n<n_0+594$, $n_0\ge1$, contains an index with $c_n<0$ and an index with $c_n>0$. Hence every run of $c_n$ has length at most $593$.
```{=latex}
\end{theorem}
```

<!-- statement
id: T4
label: CONDITIONAL
certificate: papers/keiper-li-run-torus/code/cert_c2_L594.json
-->

**Hypotheses:** RH (the zero formula). The zeros enter only through part (a) of the zero list, which C2 certifies, so the trusted count of part (b) is not used. We reuse the argument and the zero list of Theorem A of [2]; the difference is the weights.

```{=latex}
\begin{proof}
```
*Assumptions of C2, stated as facts.* (1) By the zero formula $c_n=\sum_k a_k\cos(n\theta_k)$ and the bound $|c_n-\sum_{k\le2000}2w^*_k\cos(n\theta^*_k)|\le W$ for all $n\ge1$, with the $2000$ distinct zeros $\gamma^*_k\in I_k$; this is the displayed bound above at the point $x=(n\theta_k)_k$. The zero $\gamma_1^*$ is not assumed to avoid any phase. (2) The ball enclosing $\theta^*_1$ contains the true $\theta^*_1$, so an arc computed from the ball and shrunk at both ends lies in the true arc of Lemma \ref{lem:wb}. (3) The weight vector is the same real vector for every phase of the arc and is applied to the indices $n_0+j$; every $n_0\ge1$ is covered because the phase $x^*_1=n_0\theta^*_1$ is just a point of the circle, and no equidistribution is used. (4) For all non-positive windows apply the argument to $-c_n$, that is to the point $x+\pi$, which has first phase $x^*_1+\pi$; the cover is of the whole circle, so it contains this phase as well. A window with some $c_n=0$ is covered because Lemma \ref{lem:wb} yields a strictly negative weighted sum, hence a strictly negative term.

*Proof.* Let $n_0\ge1$ and $x=(n\theta_k)_k$ with $n=n_0$, so $F_x(j)=c_{n_0+j}$ for $0\le j\le593$ by the zero formula. By C2 the open arcs $A_i$ cover the circle, so $x^*_1$ lies in some $A_i$. Lemma \ref{lem:wb} with the vector $\beta^{(i)}$ gives $j<594$ with $c_{n_0+j}<0$. Replacing $x$ by $x+\pi$, for which $F_{x+\pi}(j)=-c_{n_0+j}$, gives $j'$ with $c_{n_0+j'}>0$. A run of $594$ values of one strict sign contradicts this.
```{=latex}
\end{proof}
```

**Comparison with Theorem A of [2].** Theorem A proves the bound $621$, that is, it excludes the window $622$, with a comb: $M$ weights, the same for every phase, placed at the troughs of the first zero (about $2\pi/\theta_1$ apart), so their positions move with that phase. T4 excludes $594$ with the same zero list, the same hypothesis (RH) and the same listed zeros ($2000$ intervals); the gain of $28$ comes from the weights, which here are spread over the whole window and depend on the phase of the first zero through $48$ arcs. In the language of Section 3 the comb is a special case of a conditioned certificate (the case where $\beta$ is supported on the troughs of the first zero), and C2 is the same device with a larger family of weights. T2(b) says what limits it: a conditioned certificate for $K=2000$ and allowance $W$ exists exactly when $594>D(2000,W)$, so no conditioned certificate of this type proves less than $D(2000,W)+1$.

```{=latex}
\begin{theorem}[the bracket]\label{thm:T5}
```
Assume RH and part (b) of the zero list. Then $589\le\Lstr\le\Lclo\le593$. Consequently every run of $c_n$ has length at most $593$ (this needs RH and part (a) only), and if also $\mathrm{LI}_\theta$ holds, then $589\le\Lrh\le593$.
```{=latex}
\end{theorem}
```

<!-- statement
id: T5
label: CONDITIONAL
certificate: papers/keiper-li-run-torus/code/cert_c1_torus589.json, papers/keiper-li-run-torus/code/cert_c2_L594.json
-->

**Hypotheses:** the lower bound $589$ is T3 (RH and part (b) of the zero list). The upper bound $\Lclo\le593$ uses RH, to define $F$, and part (a) of the zero list only. The bound $589\le\Lrh$ also uses $\mathrm{LI}_\theta$ (T1(c)), and is the weakest link: under RH alone, $\Lrh$ is bounded above by $593$ but we prove no lower bound better than [2].

```{=latex}
\begin{proof}
```
*Torus bound.* Let $x\in\mathbb{T}^\infty$. By C2 the open arcs cover the circle, so $x_1^*\in A_i$ for some $i$, and Lemma \ref{lem:wb} gives $j<594$ with $F_x(j)<0$. Hence $\ell_\ge(x)\le593$ for every $x$, that is $\Lclo\le593$. The inequality $\Lstr\le\Lclo$ is T1. The lower bound $\Lstr\ge589$ is T3. For the sequence, $\Lrh\le\Lstr\le593$ by T1(b); T4 gives the same statement for $c_n$ directly, with RH and part (a) only. If $\mathrm{LI}_\theta$ holds, T1(c) gives $\Lrh=\Lstr\ge589$.
```{=latex}
\end{proof}
```

**Where the amplitude goes.** A zero of higher multiplicity, a zero that is not the first one in its interval, and all zeros beyond $2000$ enter the proof only through $W$. This is why part (b) is not needed above: part (a) says only that each $I_k$ contains a zero, and the total amplitude of everything else is at most $W$ by the definition of $C=\sum_ka_k=2\lambda_1$. If part (b) held and the first zero were pinned, nothing in C2 would change.

**Broken inputs.** Certificate C2 is tested on inputs that must fail, and each fails or is refused as stated; the list is in Appendix B. These are behaviours of the script, not statements about $c_n$.

**An independent check (C5).** A second implementation recomputes the C1 and C2 quantities in floating point, without Arb, from the stored inputs. It is a plausibility check, not a proof; its comparison with the certified values is in Appendix B. The second check of T4 is exact: C6 is an independent implementation of the C2 inequality in exact rational arithmetic that shares no code with C2. It uses the same zero list and weight vectors as inputs and does not repeat the part (a) check.

# Runs under independence

**The statement for the sequence.** T3 and T5 are statements about $F_x$. For $c_n$, Section 4 says that the lower bound $589$ needs the phases $n\theta_k$ to come near a point, for the first $1400$ zeros and also for the whole tail, because the tail does not behave as favourably as the aligned condition when only finitely many angles are controlled. The device of this section is to control the angles up to a height $\Gamma$, and to treat the zeros above $\Gamma$ as an adversarial tail of the size $T(\Gamma)=\sum_{\gamma>\Gamma}a_k$, which is small enough to be absorbed by the margin of C1.

**The tail above $\Gamma$.** Let $N(T)$ be the number of zeros with $0<\gamma\le T$ counted with multiplicity. We use the unconditional explicit estimate of Bellotti and Wong [15, Theorem 1.1, second estimate]: for $T\ge e$,
$$
\Bigl|N(T)-\frac T{2\pi}\log\frac T{2\pi e}\Bigr|\le0.11200\log T+0.12567\log\log T+3.77417 ,
$$
with the constants taken as exact rationals; we use the statement as published. By partial summation (derivation in Appendix B; the only relaxations are $\log\log t\le\log t$ and $2t/(\tfrac14+t^2)^2\le2/t^3$) this bounds $T(\Gamma)=\sum_{\gamma>\Gamma}2m_\gamma w_\gamma$ above, and bounds $N(\Gamma)$ by the main term plus the error term. Let $K'$ be the number of distinct ordinates $\gamma_k\le\Gamma$, so $K'\le N(\Gamma)$.

```{=latex}
\begin{theorem}[runs of $589$ under independence]\label{thm:T6}
```
Assume RH, part (b) of the zero list and $\mathrm{LI}_\theta(2\cdot10^5)$. By [15, Theorem 1.1] and certificate C4, the set of $n\ge1$ with $c_n,\dots,c_{n+588}>0$ has positive lower density, and so does the set with $c_n,\dots,c_{n+588}<0$. In particular runs of length at least $589$ of each sign occur, infinitely often.
```{=latex}
\end{theorem}
```

<!-- statement
id: T6
label: CONDITIONAL
certificate: papers/keiper-li-run-torus/code/cert_c4_589_G200000.json
-->

**Hypotheses:** RH; part (b) of the zero list (the first $1400$ listed zeros are the first $1400$ ordinates and are simple, as in T3); and $\mathrm{LI}_\theta(2\cdot10^5)$, which we do not prove or test. The explicit bound of [15, Theorem 1.1] is used as a published theorem. The conclusion is about $c_n$ and is conditional on these three. The tail certificate itself is certified in ball arithmetic.

**Certificate C4.** Let $y\in\mathbb{T}^{1400}$ be the phases of C1, $\kappa=294$, $L=589$, $K=1400$, and $\theta_{\mathrm{up}}$ as in T3. Let $T_K^-$ be the certified lower end of $T_{1400}$ and $T^+(\Gamma)$ the certified upper end of $T(\Gamma)$ rounded up to $2^{-70}$. Certificate C4 verifies in ball arithmetic ($128$ bits), for $\Gamma=2\cdot10^5$, that for every $0\le j\le588$
$$
F^{1400}_y(j)+\bigl(T_K^--T^+(\Gamma)\bigr)\cos\bigl(\min(|j-\kappa|\,\theta_{\mathrm{up}},\pi)\bigr)-T^+(\Gamma)\ \ge\ m,\qquad m\ge m^-=1.8540\cdot10^{-5}>0 ,
$$

where $m^-$ is the certified lower end of the margin.

The minimum is at $j=246$ (certified). Conservative reading choices: the lower end of $T_K$ is used, not a stored input; the box radius is $r=m^-/C$ with $C=2+\gamma_E-\log4\pi$ (the sum of all $a_k$, instead of the partial sum over the first $K'$ zeros); $K'$ is bounded by $M(\Gamma)+e(\Gamma)$, where $M$ and $e$ are the main and error terms of [15]. The run is described in Appendix B. No new zero computation is used: the zeros from the $1401$st to the $K'$-th enter only through the bound on $N(T)$.

| $\Gamma$ | result | $T(\Gamma)$ (upper) | density bound |
|---|---|---|---|
| $10^5$ | fails, margin $-1.323\cdot10^{-5}$ | $3.399\cdot10^{-5}$ | not computed |
| $2\cdot10^5$ | passes, margin $1.854\cdot10^{-5}$ | $1.810\cdot10^{-5}$ | $\ge10^{-1161089}$ |
| $5\cdot10^5$ | passes, margin $3.908\cdot10^{-5}$ | $7.821\cdot10^{-6}$ | $\ge10^{-2921530}$ |
| $10^6$ | passes, margin $4.646\cdot10^{-5}$ | $4.131\cdot10^{-6}$ | $\ge10^{-6105629}$ |

We use $\Gamma=2\cdot10^5$, the smallest of the four values tried that passes; the threshold $T(\Gamma)<2.736\cdot10^{-5}$ is about half the C1 margin $5.472\cdot10^{-5}$ (the C4 margin is roughly the C1 margin minus $T(\Gamma)(1+\cos)$ at the minimising $j$, and the cosine at $j=246$ is $0.9997$), and $1.810\cdot10^{-5}$ is below it; at $\Gamma=10^5$, $T(\Gamma)$ is above it and the margin is negative. The margin $1.854\cdot10^{-5}$ is $34\%$ of the margin of C1. For the earlier window $584$ the same certificate passed already at $\Gamma=10^5$ (margin $5.658\cdot10^{-7}$), and that record is kept; the longer window needs a larger $\Gamma$ because its margin is smaller. At $\Gamma=2\cdot10^5$: $K'\le298204$, $r=m^-/C\ge4.0137\cdot10^{-4}$.

```{=latex}
\begin{proof}
```
*From C4 to the theorem.* Recall $K'\le N(\Gamma)\le298204$. Define $x\in\mathbb{T}^{K'}$ by $x_k=y_k$ for $k\le1400$ and $x_k=-\kappa\theta_k$ for $1400<k\le K'$. For $k>1400$, $\theta_k\le\theta_{\mathrm{up}}$ by part (b) of the zero list, and the cosine in the alignment step below is positive because $|j-\kappa|\theta_{\mathrm{up}}\le294\,\theta_{\mathrm{up}}<\pi/2$, so the lower end of $T_{1400}-T(\Gamma)$ may be used. Let $n\ge1$ satisfy $|n\theta_k-x_k|<r$ in $\mathbb{T}$ for all $k\le K'$. For $0\le j\le588$,
$$
c_{n+j}\ \ge\ \sum_{k\le K'}a_k\cos(j\theta_k+x_k)-\sum_{k\le K'}a_k|n\theta_k-x_k|-T(\Gamma)\ >\ F_x^{K'}(j)-rC-T(\Gamma) ,
$$
using $|\cos u-\cos v|\le|u-v|$ and the strict inequality $|n\theta_k-x_k|<r$ with $a_k>0$. By the alignment lemma applied to the zeros $1400<k\le K'$, whose total amplitude is $T_{1400}-T(\Gamma)\ge T_K^--T^+(\Gamma)$,
$$
\sum_{1400<k\le K'}a_k\cos((j-\kappa)\theta_k)\ \ge\ (T_{1400}-T(\Gamma))\cos\bigl(\min(|j-\kappa|\theta_{\mathrm{up}},\pi)\bigr),
$$
so $F^{K'}_x(j)\ge F^{1400}_y(j)+(T_{1400}-T(\Gamma))\cos(\cdot)$. Combining with C4 (its left side is at least $m^-$) and $rC=m^-$: $c_{n+j}>m^--rC=0$. The same argument with the point $x+\pi$ gives $c_{n+j}<0$ for $n$ in the set $|n\theta_k-x_k-\pi|<r$.

*Density.* Under $\mathrm{LI}_\theta(\Gamma)$ the numbers $1,\theta_1/2\pi,\dots,\theta_{K'}/2\pi$ are linearly independent over $\mathbb{Q}$, so $(n\theta_1,\dots,n\theta_{K'})$ is equidistributed in $\mathbb{T}^{K'}$ by Weyl's theorem [14]. The set of $n$ above is the set of $n$ whose point falls in a box of side $2r$, of Haar measure $(r/\pi)^{K'}\ge(4.0137\cdot10^{-4}/\pi)^{298204}>10^{-1161089}$ (certified inputs); this is positive, and the set has positive lower density. The same measure is obtained for $x+\pi$. A run containing $c_n,\dots,c_{n+588}>0$ has length at least $589$.
```{=latex}
\end{proof}
```

The density bound is astronomically small; it is a positivity statement and says nothing about where a run first occurs.

**Why $\mathrm{LI}_\theta(1400)$ alone gives only a few tens (numerical).** With only the first $1400$ angles controlled, the unlisted zeros are adversarial at every $j$ (the robust tail). For the C1 phases the robust condition fails at the earlier window $584$ with margin $-2.209\cdot10^{-3}$ (certified: this is the flipped-tail failure of Appendix B, run on the $584$ phases and not repeated at $589$), and the longest window it gives is a few tens (numerical). This is why T6 needs independence to the height $2\cdot10^5$: the sum of the tail beyond a height $\Gamma$ must be below half the C1 margin (certified: C4 fails at $\Gamma=10^5$ and passes at $2\cdot10^5$).

```{=latex}
\begin{theorem}[robust-tail problem, window $534$]\label{thm:T7}
```
In the $K$-zero model (amplitudes $2w_k$ at ordinates in the intervals $I_k$, $T_K=C-\sum_{k\le K}2w_k$), the robust-tail problem has no window of $534$: $L_c(K)\le533$ for $K=2000$ (and, as a check, for $K=1400$). Hence $L_c(K)\le533$ for every $K\le2000$.
```{=latex}
\end{theorem}
```

<!-- statement
id: T7
label: PROVED
certificate: papers/keiper-li-run-torus/code/cert_c3_K2000.json, papers/keiper-li-run-torus/code/cert_c3_K1400.json
-->

**Hypotheses:** none for the statement about the $K$-zero model, which is a finite problem (the model fixes ordinates in the intervals $I_k$ and amplitudes $2w_k$). To read it as a statement about $L_c(K)$ of Section 2, which uses the true first $K$ ordinates, one needs RH and part (b) of the zero list; the comparisons below are made under them. It is not about $c_n$. It does not contradict T3, since under RH and part (b), $L_c(K)\le L_a(K)\le\Lstr$ by T1.

```{=latex}
\begin{proof}
```
**Certificate C3.** It is the robust-tail variant of the trough comb of Theorem A of [2] (the script is a copy of the script of [2] with the changes marked). The window is $L=534$, the comb has $M=6$ troughs of the first zero spaced $P_1=2\pi/\theta_1=88.848$ apart, with the sine weights $b_i=\lfloor2^{50}\sin(\pi i/(M+1))\rfloor/2^{50}$ ($i=1,\dots,M$) of [2]: $M$ weights, the same for every phase, placed at the troughs of the first zero, so their positions $n_i$ move with that phase. The guard $MP_1\le L$ passes ($MP_1\le533.089$). Claim: no $x\in\mathbb{T}^K$ has $F^K_x(j)>T_K$ for all $534$ consecutive $j$. Why C3 suffices: with the comb indices $n_i$ (the integer nearest to the $i$-th trough), $\sum_ib_iF^K_x(n_i)\le-Q_1+\sum_{k=2}^K2w_k|B_k|$, where $Q_1=2w_1\sum_ib_i\cos(\delta_i\theta_1)$ and $\delta_i$ is the rounding error of the trough position, and $B_k$ is the sum of the weights times the unit phases at $\theta_k$, as in [2]. A window with $F^K_x>T_K$ gives $\sum_ib_iF^K_x(n_i)>T_K S$ with $S=\sum b_i$. So $R_3=(\sum_{k=2}^K2w_k|B_k|-T_KS)/Q_1<1$ for every trough phase $u$ is a contradiction. $T_K$ enters at its certified lower end, so a raised $T_K$ passes more easily and is refused by the guard. Two certified evaluations of $R_3$ are recorded: a closed form (no cover) and an adaptive cover of $u\in[0,1]$ by $1024$ dyadic cells (in each cell every integer rounding compatible with it is tried, in every combination; $7$ cells are ambiguous in this sense, and a cell is split only if some combination fails).

| $K$ | closed form $R_3$ | cover, largest $R_3$ | time |
|---|---|---|---|
| $2000$ | $0.9918$ | $0.9571$ | $81$ s |
| $1400$ | $0.9409$ | $0.9062$ | $54$ s |

Both are below $1$, so $L_c(2000)<534$ (and $L_c(1400)<534$, which also follows from $K=2000$ and monotonicity). For $K<2000$, T1(a) (monotonicity of $L_c$, which uses only $T_{K+1}=T_K-a_{K+1}$) gives $L_c(K)\le L_c(2000)\le533$.
```{=latex}
\end{proof}
```

**Remark (the robust problem is the method of Theorem C).** The runs of $392$ and $476$ of [2] use independence of finitely many angles and treat the rest as adversarial, that is, a robust tail. T7 says that with the first $2000$ zeros as listed amplitudes the robust problem has no window above $533$ whatever the phases, for $K\le2000$. For large $K$ the robust problem reaches $\Lstr\ge589$ (T1(a) and T3), so the bound $533$ is a statement about at most $2000$ listed zeros; the price of reaching $\Lstr$ is independence of many more angles, which is what T6 pays (T6 is the robust problem at $K=K'$ together with the alignment of the zeros $1401$ to $K'$). Floating-point searches for robust windows are consistent with the certified $533$ (Section 7).

**Broken inputs.** C3 and C4 are tested on inputs that must fail, and each fails or is refused as stated; the list is in Appendix B.

# Numerical evidence

Everything in this section is floating point or heuristic unless a certificate label stands next to the number. None of it is used in a proof.

**The bracket against $K$.** Certificate C3 shows that the robust-tail problem (the method of Theorem C of [2]) has no window of $534$ for every $K\le2000$ (T7). Certificate C2 excludes windows of $594$ with the full dual at $K=2000$ (T4). Certificate C1 gives the aligned window $589$ at $K=1400$ (T3). Together with the lower bound $476$ of [2] at $K=1400$ (certified, under $\mathrm{LI}_\theta(1400)$), these are the values of the bracket; Figure \ref{fig:bracket} shows them against $K$. The smallest excluded window is nonincreasing in $K$ for the method that produces it; we quote the dual only at $K=2000$, where it is certified (C2).


**Primal searches.** Floating-point searches for a long window, started from random phases and improved by sequential linear programming, give the following (all numerical).

| Search | $K$ | Window | Margin |
|---|---|---|---|
| aligned tail, certified afterwards (C1) | $1400$ | $589$ | $5.472\cdot10^{-5}$ (certified) |
| aligned tail, certified afterwards (first result, C1 for the $584$ phases) | $1400$ | $584$ | $6.851\cdot10^{-5}$ (certified) |
| favourable tail | $2000$ | $552$ | $9.7\cdot10^{-4}$ (numerical) |
| robust tail | $1400$ | $477$ | $2.9\cdot10^{-5}$ (numerical) |
| robust tail | $2000$ | $489$ | $5.5\cdot10^{-6}$ (numerical) |

The robust-tail searches reach $477$ at $K=1400$ and $489$ at $K=2000$. These sit below the certified upper bound $533$ of C3 for the robust-tail problem, and the gap $489$ to $533$ (at $K=2000$) is open in the robust model, as is the gap $589$ to $593$ in the full problem (T5). A search that stops is evidence only about that search.

**No conjecture.** The runs we can produce and the dual we can certify leave $\Lstr$ in $[589,593]$ (T5). We make no conjecture about where in this bracket $\Lstr$ lies: we have no derivation that points to a value.

**Figures.** Figure \ref{fig:c2arcs} shows the arcs of C2, Figure \ref{fig:c1margin} the margin of C1, and Figure \ref{fig:bracket} the bracket against $K$. No number in the text depends on them.

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=6.4cm, xmin=0, xmax=6.2832, ymin=0.96, unbounded coords=jump, ymax=1.02, xlabel={phase $\phi$}, ylabel={$R(\phi)$},
  xtick={0,1.5708,3.1416,4.7124,6.2832}, xticklabels={$0$,$\pi/2$,$\pi$,$3\pi/2$,$2\pi$},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false]
\addplot[thin,fgblue] table[header=false, skip first n=1, x index=0, y index=1] {data/fig1-c2-arcs.dat};
\addplot[domain=0:6.2832,fgred,dashed] {1};
\node[font=\scriptsize,fgred,anchor=south west] at (axis cs:0.1,1.002) {$R=1$};
\end{axis}
\end{tikzpicture}
\caption[The arcs of C2]{The $48$ arcs of certificate C2. Each blue curve is $R(\phi)=\rho/\cos(\phi-\phi_0)$ on the arc of its weight vector, where it is below $1$ (the dashed line); $\phi$ is taken mod $2\pi$. Every phase lies in some arc, and neighbouring arcs overlap by at least $0.01709$ (certified, ball arithmetic). The largest certified $\rho$ is $0.99508$. The curves are drawn in double precision from the certified $\rho$ and arc ends.}\label{fig:c2arcs}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see 48 short blue U-shaped curves along a phase axis from 0 to 2 pi, each dipping to a value between 0.97 and 0.995 and rising to 1 at both ends, under a dashed red horizontal line at 1. Neighbouring curves overlap, so together they cover the whole axis.
-->

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=6cm, xmin=-5, xmax=595, ymin=-0.002, ymax=0.034, xlabel={$j$}, ylabel={margin},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false, yticklabel style={/pgf/number format/fixed,/pgf/number format/precision=3}]
\addplot[thick,fgblue] table[header=false, skip first n=1, x index=0, y index=1] {data/fig2-c1-margin.dat};
\addplot[domain=-5:595,fgred,dashed] {0};
\addplot[only marks,mark=o,mark size=2.6pt,fgred,thick] coordinates {(246,0.0000547)};
\draw[fgred,thin] (axis cs:246,0.0015) -- (axis cs:246,0.0275);
\node[font=\scriptsize,fgred,anchor=south] at (axis cs:246,0.0275) {minimum $5.472\cdot10^{-5}$ at $j=246$};
\end{axis}
\end{tikzpicture}
\caption[The margin of C1]{The margin of certificate C1 at $K=1400$: $F^{1400}_y(j)+T^{-}_{1400}\cos(\min(|j-\kappa|\theta_{\mathrm{up}},\pi))$ for $j=0,\dots,588$ (blue), against zero (red, dashed). The certified quantity is the minimum over $j$, computed in ball arithmetic: $5.472\cdot10^{-5}>0$ at $j=246$. The curve is plotted in double precision (numerical).}\label{fig:c1margin}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see a blue curve for j from 0 to 588 that stays above a dashed red line at zero. It rises to about 0.02 near the two ends and wiggles low in the middle, and the closest approach to zero is circled at j equal to 246, with margin 5.47 times ten to the minus five.
-->

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=6.4cm, xmin=1000, xmax=2300, ymin=440, ymax=620, xtick={1000,1200,1400,1600,1800,2000,2200}, xlabel={number of zeros $K$}, ylabel={run length},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false]
\addplot[only marks,mark=*,mark size=2pt,fgblue] coordinates {(1400,476) (1400,589)};
\addplot[only marks,mark=triangle*,mark size=2.6pt,fgred] coordinates {(2000,593)};
\addplot[only marks,mark=square*,mark size=2pt,gray] coordinates {(1400,533) (2000,533)};
\addplot[only marks,mark=o,mark size=4.5pt,thick,black] coordinates {(1400,477) (2000,489)};
\node[font=\scriptsize,fgblue,anchor=west] at (axis cs:1430,476) {$476$ (previous paper)};
\node[font=\scriptsize,fgblue,anchor=west] at (axis cs:1430,583) {$589$ (C1)};
\node[font=\scriptsize,fgred,anchor=south east] at (axis cs:2290,597) {$593$ (C2)};
\node[font=\scriptsize,gray,anchor=south east] at (axis cs:2290,536) {$533$ (C3, robust-tail problem)};
\node[font=\scriptsize,anchor=east] at (axis cs:1370,477) {$477$ (robust search)};
\node[font=\scriptsize,anchor=west] at (axis cs:2030,489) {$489$ (robust search)};
\node[font=\scriptsize,gray,anchor=east] at (axis cs:1370,533) {$533$};
\end{axis}
\end{tikzpicture}
\caption[The bracket against $K$]{The values of the bracket against the number of zeros $K$. Blue dots: certified values, $476$ ([2], $K=1400$, under RH and $\mathrm{LI}_\theta(1400)$) and $589$ (C1, $K=1400$, torus value, under RH and part (b)). Red triangle: certified upper bound $593$ (C2, $K=2000$, under RH). Grey squares: certified upper bound $533$ of the robust-tail problem (C3), at $K=1400$ and $K=2000$. Large open circles: the numerical robust-tail search, $477$ ($K=1400$) and $489$ ($K=2000$), not a certificate. The bracket $589$ to $593$ is for the torus problem with all zeros and does not depend on $K$; it is not drawn as a band.}\label{fig:bracket}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see run length against the number of zeros K, from 1000 to 2300. At K equal to 1400 two blue dots sit at 476 and 589. At K equal to 2000 a red triangle sits at 593. Grey squares at 533 sit at both K; open circles sit at 477 for K equal to 1400 and 489 for K equal to 2000.
-->

# Remarks

**What is open.** The width of the bracket $589\le\Lstr\le\Lclo\le593$ (T5) is open: five values. We never call the bracket closed. For $c_n$ itself, the lower bound $589\le\Lrh$ needs $\mathrm{LI}_\theta$ (T1, T5), and the sharper reading $\Lrh=\Lstr$ needs it too.

**What would close it.** Three routes, none done. (i) Condition on two phases instead of one: the dual of T2 weights by the first phase only, and using the first two zeros as free parameters would shrink the largest ratio the cover has to beat, at the price of a two-dimensional cover. (ii) A semidefinite relaxation of the torus problem, in the spirit of [11], which would give a certificate for windows below $594$ if the relaxation is tight enough; we have not tried it. (iii) Longer primal searches with the favourable and aligned tails at $K=2000$, which could lift the certified lower bound above $589$ through a new instance of C1; the favourable-tail search at $K=2000$ reached $552$ and the aligned-tail push at $K=2000$ reached $589$ with float margin $5.0\cdot10^{-5}$, not certified (numerical).

**Prior art.** Prior art and what is new are in Section 1. We make no claim of novelty for weak duality, for the cone program step, or for the convex analysis, which are classical [4]. The closest earlier methods are the almost periodic argument of Haraux [5] and the iterated averaging comb of Kozma and Oravecz [6].

**Alpöge.** The remark in Section 1 on the announced proof of RH applies unchanged: it would remove RH from T1 to T5 but not $\mathrm{LI}_\theta$.

# Code and data {-}

The certificate scripts, their inputs, the zero list and the certificate records of C1 to C4 and the second check C6 are archived at <https://github.com/mik-tf/keiper-li-run-torus> and on Zenodo, <https://doi.org/10.5281/zenodo.24517615> (concept DOI, all versions). Appendix B explains how to reproduce each certificate.

# Use of AI {-}

Claude Opus 5.5 and Claude Sonnet 5.5 (Anthropic) were used in November 2026, under the author's direction, for exploratory computation, derivations, code, checks, literature search and drafting.

# Appendix A: what each certificate checks {-}

The proofs of T1, T2 and the alignment lemma are in the main text. This appendix states, in one place, the inequality that each certificate checks in ball arithmetic. A certificate proves its inequality for the archived exact inputs; the theorem that uses it carries the hypotheses listed in the table of Section 1.

**C1 (T3, $K=1400$, $L=589$).** With the archived phases $y$ (integers over $2^{40}$) and the tail amplitude $T^{-}_{1400}$ (the certified lower end of $T_{1400}$), for every $j=0,\dots,588$:
$$F^{1400}_y(j)+T^{-}_{1400}\cos(|j-\kappa|\theta_{\mathrm{up}})>0 .$$
The certified minimum is $5.472\cdot10^{-5}$ at $j=246$.

**C2 (T4, $K=2000$, $L=594$).** For a window $n_0,\dots,n_0+L-1$ and weights $\beta_j\ge0$ supported on the whole window, $S=\sum_j\beta_j$ and $B(\theta)=\sum_j\beta_je^{ij\theta}$, $B_1=B(\theta^*_1)$,
$$\sum_j\beta_jc_{n_0+j}\le2w^*_1\,\mathrm{Re}\bigl(e^{i\phi}B_1\bigr)+H,\qquad H=\sum_{k=2}^{2000}2w^*_k|B(\theta^*_k)|+WS,$$
with $\phi$ the unknown phase of the first zero. On $|\phi-\phi_0|<\arccos\rho$, where $\rho=H/(2w^*_1|B_1|)$ and $\phi_0=-\arg B_1-\pi$, the right side is negative, so an all-nonnegative window is impossible there; the phase $\phi+\pi$ handles the all-nonpositive case, which is why the whole circle is covered. The certificate checks that every one of the $48$ vectors has $\rho<1$ (certified maximum $0.99508$) and that the $48$ open arcs, a chain of $22$ of them, cover $[0,2\pi]$ with smallest overlap $0.01709$ rad. Four facts are used and nothing else: (1) the zero formula with tail bound $W=C-2\sum_{k\le2000}w^*_k$ and the $2000$ zero intervals each holding a zero of odd multiplicity (part (a) of the zero list); (2) $B_1$ is evaluated with $\theta^*_1$ as a ball; (3) the weights are one real vector for the whole arc; (4) windows with some $c_n=0$ are covered because the weighted sum is strictly negative. The vectors come from a floating-point program and are inputs, so how they were found does not matter. The upper end of $W$ is $8.847\cdot10^{-4}$.

**C3 (T7, $K\le2000$, window $534$).** The robust comb with $M=6$ troughs: a closed form $R_3=0.9918$ at $K=2000$ and $0.9409$ at $K=1400$, and a cover of $1024$ cells with $R_{3,\max}=0.9571$ at $K=2000$ ($7$ cells with more than one compatible rounding, all combinations tried in each) and $0.9062$ at $K=1400$. The certificate refuses window $533$, since $M P_1$ has upper end $533.089$.

**C4 (T6, $\Gamma=2\cdot10^5$).** With the phases of C1 and $K=1400$,
$$\min_{0\le j\le588}\Bigl[F^{1400}_y(j)+(T_{1400}-T(\Gamma))\cos\bigl(\min(|j-\kappa|\theta_{\mathrm{up}},\pi)\bigr)\Bigr]-T(\Gamma)>0 .$$
The bound $T(\Gamma)\le1.810\cdot10^{-5}$ is obtained by partial summation from the explicit bound for $N(T)$ in [15, Theorem 1.1, second estimate], valid for $T\ge e$, with constants as exact rationals; the only relaxations are $\log\log t\le\log t$ and $2t/(1/4+t^2)^2\le2/t^3$ (the derivation is in Appendix B). The number $K'$ of distinct ordinates up to $\Gamma$ is at most $298204$. The box radius around the target phases is $r=m^-/C\ge4.0137\cdot10^{-4}$ and, under $\mathrm{LI}_\theta(2\cdot10^5)$, the density of the runs is at least $(r/\pi)^{K'}\ge(r/\pi)^{298204}\ge10^{-1161089}$. The certified margin is $1.854\cdot10^{-5}$ at $j=246$ ($34\%$ of the C1 margin).

**C5 (cross-check, not a proof).** An independent floating-point implementation, with no Arb and no import of the certificate scripts, recomputes the values of C1 to C4 from the stored midpoints, integer phases and weights.

# Appendix B: reproduction {-}

Python $3.12$ with python-flint $0.9.0$ [16] (Arb, $128$-bit balls), and numpy [18] and mpmath [17] for C5. The scripts, inputs and certificate records are archived at <https://github.com/mik-tf/keiper-li-run-torus> and on Zenodo, <https://doi.org/10.5281/zenodo.24517615>. Scripts and archives are in `code/`; the commands below are run in that directory. Inputs are exact integers: phases over $2^{40}$, $T_{\mathrm{used}}$ over $2^{60}$, the weights of C2 over $2^{50}$. Each certificate file stores its run record (UTC time, script and input hashes, result). The zero list `z2000.json` is the file of [2]. Timings are wall-clock seconds as measured.

- C1 (T3): `python3 certify_torus584.py z2000.json inputs_c1_589.json OUT/cert_c1_torus589.json` (about $45$ s on a loaded machine; peak memory about $31$ MB). Certified minimum margin $5.472\cdot10^{-5}$ at $j=246$. The script name is historical; the window is read from the inputs. The inputs are made from the search output by `make_inputs_c1_L.py`. The earlier window $584$ (`inputs_c1.json`, `cert_c1_torus584.json`, minimum $6.851\cdot10^{-5}$ at $j=245$, $6.7$ s) is kept in the archive.
- C2 (T4): `python3 certify_c2.py z2000.json 594 vectors_c2.json OUT/cert_c2_L594.json --jobs 4` (about $22$ s on $4$ processes; peak memory about $34$ MB per process). The script requires every vector to have exactly $594$ weights.
- C3 (T7): `python3 certify_comb_rob.py z2000.json 534 6 sine 2000 robust OUT/cert_c3_K2000.json` (about $81$ s) and the same with $1400$ in place of $2000$ (about $54$ s). Peak memory about $34$ MB.
- C4 (T6): `python3 certify_tail_c4.py z2000.json inputs_c1_589.json inputs_c4_200000.json OUT/cert_c4_589_G200000.json` (about $31$ s on a loaded machine; peak memory about $30$ MB). The inputs for other $\Gamma$ are made by `make_inputs_c4.py`; the bound is implemented in `nt_bound.py` and derived below. The record for the $584$ phases at $\Gamma=10^5$ is `cert_c4_G100000.json`.
- C5: `python3 crosscheck_c5.py . --c1-inputs inputs_c1_589.json --c1-cert cert_c1_torus589.json --c4-cert cert_c4_589_G200000.json --json OUT/crosscheck_c5_589.json` (about $3$ s). It reads only the stored midpoints, phases and weights. Without the three options it checks the $584$ run.
- C6 (T4, second check): `python3 certify_c6.py z2000.json 594 vectors_c2.json OUT/cert_c6_L594.json --jobs 4` (about $141$ s on $4$ processes on a loaded machine; peak memory about $21$ MB). It passes with maximum $\rho=0.995073989$ against $0.9950736714$ for C2. It does not recheck part (a) of the zero list.

**The bound for $T(\Gamma)$ and $N(\Gamma)$.** Write $f(t)=1/(\tfrac14+t^2)$, $N(t)$ as in Section 6, $M(t)=\frac t{2\pi}\log\frac t{2\pi e}$ and $e(t)=a\log t+b\log\log t+c$ with $a=0.11200$, $b=0.12567$, $c=3.77417$ taken as exact rationals, so that $M(t)-e(t)\le N(t)\le M(t)+e(t)$ for $t\ge e$ by [15, Theorem 1.1, second estimate]. Let $\Gamma\ge e$ be given. Counting zeros with multiplicity, $T(\Gamma)=2\sum_{\gamma>\Gamma}f(\gamma)$. Since $f$ is decreasing and $N(t)f(t)\to0$, Stieltjes integration by parts gives
$$\tfrac12T(\Gamma)=-f(\Gamma)N(\Gamma)+\int_\Gamma^\infty N(t)\,(-f'(t))\,dt,\qquad -f'(t)=\frac{2t}{(\frac14+t^2)^2}\le\frac2{t^3}.$$
Now $-f'>0$ and $0\le N(t)\le M(t)+e(t)$, so the integral is at most $\int_\Gamma^\infty(M+e)\,2t^{-3}dt$, and $N(\Gamma)\ge M(\Gamma)-e(\Gamma)$ bounds the boundary term. With $\int_\Gamma^\infty t^{-2}dt=1/\Gamma$, $\int_\Gamma^\infty t^{-2}\log t\,dt=(\log\Gamma+1)/\Gamma$ and $\int_\Gamma^\infty 2t^{-3}\log t\,dt=\log\Gamma/\Gamma^2+1/(2\Gamma^2)$, and with the relaxation $\log\log t\le\log t$ in the integral only (the boundary term keeps $\log\log\Gamma$),
$$T(\Gamma)\le2\Bigl[-\bigl(M(\Gamma)-e(\Gamma)\bigr)f(\Gamma)+\frac{\log\Gamma-\log2\pi}{\pi\,\Gamma}+(a+b)\Bigl(\frac{\log\Gamma}{\Gamma^2}+\frac1{2\Gamma^2}\Bigr)+\frac c{\Gamma^2}\Bigr].$$
The middle term is $\int_\Gamma^\infty M(t)\,2t^{-3}dt$. The script `nt_bound.py` evaluates the right side in ball arithmetic and rounds up. Likewise $K'\le N(\Gamma)\le M(\Gamma)+e(\Gamma)$. Only the cited estimate [15] is used; its proof is not reproduced here.

**Broken inputs.** Each certificate was run on inputs that must fail. All of the following failed as stated (logs in `runs/`, inputs in `broken/`).

| Certificate | Input | Result |
|---|---|---|
| C1 | window $585$, the $584$ phases | fails, margin $-6.2\cdot10^{-4}$ |
| C1 | phase of the first zero moved by $0.1$ (run on the window-$584$ phases, not rerun at $589$) | fails, margin $-4.0\cdot10^{-4}$ |
| C1 | tail sign flipped (robust instead of aligned tail; window-$584$ phases, not rerun at $589$) | fails, margin $-2.209\cdot10^{-3}$ |
| C1 | a zero midpoint moved (run on the window-$584$ inputs, not rerun at $589$) | fails the check on $Z$ at interval $100$ |
| C1 | $T_{1400}$ raised | refused by a guard |
| C2 | vectors truncated to $593$ weights, $L=593$ | fails, vector $26$ has $\rho\ge1$ ($1.00054$) |
| C2 | $4$ consecutive vectors removed | fails, coverage gap at $\phi=2.7269$ |
| C2 | $W$ raised to $2\cdot10^{-3}$, $5\cdot10^{-3}$, $2\cdot10^{-2}$, $5\cdot10^{-2}$ | fails, $\rho$ of vector $0$ is $1.084$, $1.387$, $2.901$, $5.929$ |
| C2 | $W$ below its upper end (including a flipped sign) | refused by a guard |
| C2 | one weight of vector $0$ set to $2^{50}$, or $100$ weights zeroed | fails, $\rho=1.301$ and $1.338$ |
| C3 | favourable sign at $M=6$ | fails, $R_3=1.169$ |
| C3 | window $533$ | refused, $M P_1$ has upper end $533.089$ |
| C3 | $T_K$ raised by $1/100$ | refused by a guard |
| C4 | $\Gamma=10^5$, the $589$ phases | fails, margin $-1.323\cdot10^{-5}$ |
| C4 | $\Gamma=5\cdot10^4$, the $584$ phases | fails, margin $-5.857\cdot10^{-5}$ |
| C4 | main term of $N(T)$ scaled by $0.8$, $\Gamma=10^5$ and $2\cdot10^5$ (run on the $584$ phases; the guard does not read them) | refused by the guard  |

Three inputs that we tried do **not** fail and are not valid broken inputs. On the window-$584$ phases (not rerun at $589$), moving the phase of the first zero by $0.01$ leaves the C1 margin positive ($5.29\cdot10^{-5}$), since the margin has slack. Removing one or two vectors from C2 still passes, since the arcs are redundant ($3.22$ coverings of the circle on average); removing $4$, $6$ or $8$ consecutive vectors gives the same gap. Mild changes to vector $0$ of C2 (first $40$ weights zeroed, a shift by one, alternate weights times $0.99$, reversed order) still pass.

**The second implementation C5.** It agrees with every certified value within a first-order radius of the zero-interval balls, widened by $1.5$ because the radius of Arb's complex absolute value of a rectangular ball is at most $\sqrt2$ times the first-order radius (the difference of C2 at the vector of largest $\rho$ is $2.3\cdot10^{-6}$ inside the radius $3.5\cdot10^{-6}$; over all $48$ vectors the largest difference is $2.57\cdot10^{-6}$ and the largest radius $3.63\cdot10^{-6}$, on different vectors), and every certified value is on the safe side. C1 minimum margin $5.47216\cdot10^{-5}$ at $589$ (float $5.47298\cdot10^{-5}$, difference $8.1\cdot10^{-9}$); C2 maximum $\rho=0.995074$ (float $0.995071$), all $48$ arcs within radius, and the float arcs cover the circle even shrunk by that radius; C3 closed form $0.940928$ and $0.991767$, cover $\sup R_3$ $0.906239$ and $0.957056$ above the float values $0.906207$ and $0.957023$ in all $1024$ cells; C4 margin $1.85403\cdot10^{-5}$ at $\Gamma=2\cdot10^5$ (float $1.85484\cdot10^{-5}$), and the float margin at $\Gamma=5\cdot10^4$ is negative, as the certified failure at $\Gamma=10^5$ implies. C5 is a check of the implementation, not an independent proof: it shares the inputs.

# References {-}

[1] J. B. Keiper, *Power series expansions of Riemann's $\xi$ function*, Math. Comp. 58 (1992), no. 198, 765-773. https://doi.org/10.1090/S0025-5718-1992-1122072-5

[2] M. Perreault, *Sign runs and the density of sign changes of Keiper-Li second differences*, 2026, Zenodo, concept DOI https://doi.org/10.5281/zenodo.24486137.

[3] F. Johansson, *Arb: efficient arbitrary-precision midpoint-radius interval arithmetic*, IEEE Trans. Comput. 66 (2017), no. 8, 1281-1292. https://doi.org/10.1109/TC.2017.2690633

[4] S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §2.5.1, §4.4.2, §5.2.3. https://web.stanford.edu/~boyd/cvxbook/

[5] A. Haraux, *Uniform oscillation properties of almost periodic functions*, arXiv:2610.06515 (5 Oct 2026), Theorem 2.1 and Theorem 3.1.

[6] G. Kozma and F. Oravecz, *On the gaps between zeros of trigonometric polynomials*, Real Anal. Exchange 28 (2002/03), arXiv:math/0601021 (Theorem 1 is an iterated two-point averaging comb).

[7] D. V. Gorbachev, V. I. Ivanov and S. Yu. Tikhonov, *Uncertainty principles for eventually constant sign bandlimited functions*, arXiv:1904.11328, §1.1 (Logan's problems; B. F. Logan, *Extremal problems for positive-definite bandlimited functions I, II*, SIAM J. Math. Anal. 14 (1983)).

[8] A. D. Gilbert and C. J. Smyth, *Zero-mean cosine polynomials which are non-negative for as long as possible*, J. London Math. Soc. (2) 62 (2000), no. 2, 489-504. https://doi.org/10.1112/S0024610700001216.

[9] M. Rubinstein and P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994), no. 3, 173-197. https://doi.org/10.1080/10586458.1994.10504289.

[10] A. Bose and R. Simpson, *Rubinstein and Sarnak: a turning point in comparative prime number theory*, course overview, https://personal.math.ubc.ca/~gerg/teaching/613-Winter2023/RSTPCPNT.pdf, §§2 and 3.

[11] A. Chirre, F. Gonçalves and D. de Laat, *Pair correlation estimates for the zeros of the zeta function via semidefinite programming*, arXiv:1810.08843 (v2, 2019), §4.

[12] L. Alpöge, untitled announcement (PDF, 5 pages), 20 November 2026, not peer reviewed, <https://alpo.ge/remark.pdf>. Lean source: <https://alpo.ge/lean.tar.gz.part01> to `lean.tar.gz.part14`; mirror <https://github.com/Deicyde/riemann-hypothesis>, commit 40e56bab. Accessed 23 November 2026.

[13] Lean FRO and Mathlib Initiative, *Lean verification of the Riemann Hypothesis*, blog post, 21 November 2026, <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>. Accessed 23 November 2026.

[14] H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. 77 (1916), 313-352.

[15] C. Bellotti and P.-J. Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, arXiv:2412.15470 (v2, 2025), Theorem 1.1.

[16] F. Johansson et al., *python-flint*, Python bindings for FLINT and Arb, version 0.9.0, https://github.com/flintlib/python-flint

[17] The mpmath development team, *mpmath: a Python library for arbitrary-precision floating-point arithmetic*, https://mpmath.org

[18] C. R. Harris et al., *Array programming with NumPy*, Nature 585 (2020), 357-362. https://doi.org/10.1038/s41586-020-2649-2
