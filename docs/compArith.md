---
header-includes:
	- \usepackage{ucs}
 	- \usepackage[utf8x]{inputenc}
 	- \usepackage{autofe}
	- \usepackage{stmaryrd}
	- \newcommand{\bb}{\mathbb{B}}
	- \newcommand{\fst}{\mathsf{fst}}
	- \newcommand{\snd}{\mathsf{snd}}

---

# compArith notes


-	$\bb$ is defined as a finite set with two elements `Fin 2`.

-	Simplified the def of $\llbracket-\rrbracket$ to just $\Sigma_{i = 0}^{i = k} x_i * 2^i$, which is implemented for vectors as:
	


	\begin{align*}
	\Sigma\ [\ ] &= 0\\
	\Sigma\ (0 :: xs^k) &= \Sigma\ xs^k\\
	\Sigma\ (1 :: xs^k) &= 2^k + \Sigma\ xs^k
	\end{align*}

	where $x^k$ is a vector of booleans of size $k$ (\texttt{Vec $\bb$ k} in agda).

-	Use $\langle\langle-\rangle\rangle$ instead of $\llparenthesis-\rrparenthesis$ because agda does not support such symbol

-	Defined $MOD\ 2$ as \texttt{\_mod$\bb$}:
	\begin{align*}
	0\ \texttt{mod$\bb$} &= 0\\
	suc\ 0\ \texttt{mod$\bb$} &= 1\\
	suc\ (suc\ a)\ \texttt{mod$\bb$} &= a
	\end{align*}

-	Defined $DIV\ 2$ as \texttt{\_div$\bb$}:
	\begin{align*}
	0\ \texttt{div$\bb$} &= 0\\
	suc\ 0\ \texttt{div$\bb$} &= 0\\
	suc\ (suc\ a)\ \texttt{mod$\bb$} &= 1
	\end{align*}

	Since we only ever do $(a + b + c) DIV\ 2$ where $a,b,c \in \bb$, we can show that $(a + b + c)\ \texttt{div}\bb \equiv (a + b + c)\ DIV\ 2$ (lemma \texttt{div$\bb$spec})

-	Defined bitwise addition of two vectors $a, b$ of the same length $k$ as a tuple $(rs,c)$, where $rs$ is the resulting vector of length $k$ and $c$ is the _carry_ $c_{k+1}$.

	\begin{align*}
	[\ ] \oplus [\ ] &= ([\ ],\ 0)\\
	(a :: as) \oplus (b :: bs) &= (r :: \fst\ (as \oplus bs), c)\\
	\text{where}&\\
	r &= (a + b + \snd\ (as \oplus bs))\ \texttt{mod$\bb$}\\
	c &= (a + b + \snd\ (as \oplus bs))\ \texttt{div$\bb$}
	\end{align*}
