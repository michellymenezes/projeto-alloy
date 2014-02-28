module empresaDeSeguranca


open util/ordering[Time]

// ASSINATURAS
sig Time{}



sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set Casa
}
sig Funcionario {}

sig Casa{
	servicos: set Servico
}
sig autoBranco extends bairro{}

sig centro extends bairro{}

abstract sig Servico{}
sig Cerca extends Servico{
disparando: Equipe lone -> Time
}
one sig Ronda extends Servico{}

one sig Monitoramento extends Servico{
funcionarios: set Funcionario
}

abstract sig StatusDaEquipe{}
one sig Ocupada, Desocupada extends StatusDaEquipe{}

sig Equipe {
	 situacao: StatusDaEquipe -> Time,
     verificando: Cerca lone -> Time
}



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



// ..:: FATO CASA ::..

fact sobreCasa{
	// casas possuem ou não algum serviço de segurança
	all c: Casa| #c.servicos >= 0
	all c: Casa| #c.servicos <= 3

	// não existe casa sem bairro
	all c: Casa | c in bairro.casas

	// uma casa não está em dois bairros
	all b1: bairro, b2: bairro, c: Casa | casaEmBairro[b1, b2, c]
}


// FATOS DO SISTEMA

fact {
	all m: Monitoramento | #m.funcionarios >=2
	#Equipe =3
	// unica cerca por casa 
	all c: Cerca | some k: Casa | c in k.servicos
	all r: Ronda | some k: Casa | r in k.servicos
	all c: Cerca, k1: Casa, k2: Casa | cadaCercaExclusivaPraUmaCasa[c, k1, k2]
	all c1: Cerca, c2: Cerca, k: Casa | cadaCasaPossuiUmaCerca[c1, c2, k]
    all c1: Cerca, c2: Cerca, e: Equipe, t: Time | cadaCercaDisparaUmaEquipe[c1, c2, e, t]
    all e1: Equipe, e2: Equipe, k: Cerca, t: Time | cadaEquipeVerificaUmaCerca[e1, e2, k, t]
	all r1: Ronda, k: Casa |  some c2: Cerca | soTemRondaSeTiverCerca[r1, c2, k]
	//all r1: Ronda, r2: Ronda, k: Casa | cadaCasaPossuiUmaRonda[r1, r2, k]
	//all r: Ronda, k1: Casa, k2: Casa | cadaRondaExclusivaPraUmaCasa[r, k1, k2]

   all r: Ronda | some k: Casa | r in k.servicos implies (some q: Cerca | q in k.servicos)
	cadaEquipeEstaVerificandoNoMaximoCerca
    equipeOcupadaQuandoVerificando
}

// ..:: PREDICADOS ::..

// cada casa só pertence a um bairro
pred casaEmBairro[b1: bairro, b2: bairro, c: Casa]{
	b1 != b2 => (c in b1.casas => c !in b2.casas)
}

pred cadaCercaExclusivaPraUmaCasa[c: Cerca, k1: Casa, k2: Casa]{
	k1 != k2 => (c in k1.servicos => c !in k2.servicos)
}

pred cadaRondaExclusivaPraUmaCasa[r: Ronda, k1: Casa, k2: Casa]{
	k1 != k2 => (r in k1.servicos => r !in k2.servicos)
}

pred cadaCasaPossuiUmaCerca[c1: Cerca, c2: Cerca, k: Casa]{
	c1 != c2 => (c1 in k.servicos => c2 !in k.servicos)
}

pred cadaCercaDisparaUmaEquipe[c1: Cerca, c2: Cerca, e: Equipe, t: Time]{
	 c1 != c2 => ( e in c1.disparando.t => e !in c1.disparando.t )
}

pred cadaEquipeVerificaUmaCerca[e1: Equipe, e2: Equipe, k: Cerca, t: Time]{
	e1 != e2 => ( k in e1.verificando.t => k !in e1.verificando.t )
}

pred soTemRondaSeTiverCerca[r1: Ronda, c2: Cerca, k: Casa]{
	r1 in k.servicos =>  c2 in k.servicos
}

pred cadaCasaPossuiUmaRonda[r1: Ronda, r2: Ronda, k: Casa]{
	r1 != r2 => (r1 in k.servicos => r2 !in k.servicos)
}

pred cadaEquipeEstaVerificandoNoMaximoCerca[]{
	all e: Equipe, t: Time |
	lone cercaQueEquipeEstaVerificando[e, t]
}

pred equipeOcupadaQuandoVerificando[]{
	all e: Equipe, t: Time | some  c: Cerca | e in c.disparando .t 
	implies
		e.situacao.t = Ocupada
	else
		e.situacao.t = Desocupada
}



fun cercaQueEquipeEstaVerificando[e: Equipe, t: Time]: lone Cerca{
	e.verificando.t
}


pred show[]{}
run show for 3 but 30 Cerca, 5 Casa
