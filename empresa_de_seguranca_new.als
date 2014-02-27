module empresaDeSeguranca

//open util/ordering[Time]
//sig Time{}

sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set Casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// ..:: FATO SISTEMA ::..

fact sobreSistema{
	// existe apenas um sistema
	one sistema
}

// ..:: FATO BAIRRO ::..

fact sobreBairro {
	// cada bairro possui, no mínimo, uma casa
	all a: autoBranco| #a.casas >= 1
	all c: centro| #c.casas >= 1
	// existem dois bairros
	all s: sistema | #s.bairros = 2
	// existe apenas um bairro de cada
	one autoBranco
	one centro
	// bairro é ou auto branco ou centro
	bairro = autoBranco + centro
}

sig Casa{
	servicos: set Servico
}

// ..:: FATO CASA ::..

fact sobreCasa{
	// casas possuem ou não algum serviço de segurança
	all c: Casa| #c.servicos >= 0
	all c: Casa| #c.servicos <= 1

	// não existe casa sem bairro
	all c: Casa | c in bairro.casas

	// uma casa não está em dois bairros
	all b1: bairro, b2: bairro, c: Casa | casaEmBairro[b1, b2, c]
}

// ..:: PREDICADOS ::..

// cada casa só pertence a um bairro
pred casaEmBairro[b1: bairro, b2: bairro, c: Casa]{
	b1 != b2 => (c in b1.casas => c !in b2.casas)
}

pred cadaCercaExclusivaPraUmaCasa[c: Cerca, k1: Casa, k2: Casa]{
	k1 != k2 => (c in k1.servicos => c !in k2.servicos)
}

pred cadaCasaPossuiUmaCerca[c1: Cerca, c2: Cerca, k: Casa]{
	c1 != c2 => (c1 in k.servicos => c2 !in k.servicos)
}

abstract sig Servico{}
sig Cerca extends Servico{}
one sig Camera, Ronda extends Servico{}

fact {
	// unica cerca por casa 
	all c: Cerca | some k: Casa | c in k.servicos
	all c: Cerca, k1: Casa, k2: Casa | cadaCercaExclusivaPraUmaCasa[c, k1, k2]
	all c1: Cerca, c2: Cerca, k: Casa | cadaCasaPossuiUmaCerca[c1, c2, k]
	all r: Ronda | some k: Casa | r in k.servicos implies (some q: Cerca | q in k.servicos)
	all c: Camera | some k: Casa | c in k.servicos implies (some q: Cerca | q in k.servicos)
//	all c: Camera | some k: Casa | c in k.servicos
}

pred show[]{}
run show for 15// but 30 Cerca, 5 Casa
