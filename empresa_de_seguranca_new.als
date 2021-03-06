module empresaDeSeguranca


open util/ordering[Time] as ord

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
situacao: StatusDaCerca one -> Time,
disparando: Equipe lone -> Time
}
one sig Ronda extends Servico{}

one sig Monitoramento extends Servico{
funcionarios: set Funcionario -> Time
}

abstract sig StatusDaEquipe{}
one sig Ocupada, Desocupada extends StatusDaEquipe{}

abstract sig StatusDaCerca{}
one sig Disparada, EmSeguranca extends StatusDaCerca{}

sig Equipe {
	 situacao: StatusDaEquipe one -> Time,
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
 
  	equipeOcupadaQuandoVerificandoCerca
	equipeNaoVerificaUmaCercaSegura
   	
	// Todo momento deve ter pelo menos 2 funcionarios monitorando
   all t: Time, c: Cerca| some e: Equipe | Disparada in c.situacao.t  => e.situacao.t = Ocupada
	all m: Monitoramento, t: Time, f: Funcionario | f in m.funcionarios.t => f not in m.funcionarios.(t.next)
	all c: Cerca, t: Time | some c.situacao.t 
    #Equipe = 3
	// unica cerca por casa 
	all c: Cerca | some k: Casa | c in k.servicos
	all r: Ronda | some k: Casa | r in k.servicos
	all c: Cerca, k1: Casa, k2: Casa | cadaCercaExclusivaPraUmaCasa[c, k1, k2]
	all c1: Cerca, c2: Cerca, k: Casa | cadaCasaPossuiUmaCerca[c1, c2, k]
    all c1: Cerca, c2: Cerca, e: Equipe, t: Time | cadaCercaDisparaUmaEquipe[c1, c2, e, t]
   all e1: Equipe, e2: Equipe, k: Cerca, t: Time | cadaEquipeVerificaUmaCerca[e1, e2, k, t]
	all r1: Ronda, k: Casa |  some c2: Cerca | soTemRondaSeTiverCerca[r1, c2, k]
	all m1: Monitoramento, k: Casa |  some c2: Cerca | soTemMonitoramentoSeTiverCerca[m1, c2, k]
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
	 c1 != c2 => ( e in c1.disparando.t => e !in c2.disparando.t )
}

pred cadaEquipeVerificaUmaCerca[e1: Equipe, e2: Equipe, k: Cerca, t: Time]{
	e1 != e2 => ( k in e1.verificando.t => k !in e2.verificando.t )
}

pred soTemRondaSeTiverCerca[r1: Ronda, c2: Cerca, k: Casa]{
	r1 in k.servicos =>  c2 in k.servicos
}

pred soTemMonitoramentoSeTiverCerca[m1: Monitoramento, c2: Cerca, k: Casa]{
	m1 in k.servicos =>  c2 in k.servicos
}

// SE UMA EQUIPE ESTA EM UMA CERCA DEVE ESTAR OCUPADA
pred equipeOcupadaQuandoVerificandoCerca[]{
	all c: Cerca, t: Time , e: Equipe | e in c.disparando.t => e.situacao.t = Ocupada
	all c: Cerca, t: Time,  e: Equipe | Disparada in c.situacao.t && e in c.disparando.t => e.situacao.t = Ocupada

 }

// UMA CERCA SEGURA NÃO DEVE TER EQUIPE NO LOCAL
pred equipeNaoVerificaUmaCercaSegura[]{
	all c: Cerca, t: Time, e: Equipe | EmSeguranca in c.situacao.t => e !in c.disparando.t 
 }


pred cadaCasaPossuiUmaRonda[r1: Ronda, r2: Ronda, k: Casa]{
	r1 != r2 => (r1 in k.servicos => r2 !in k.servicos)
}

pred cadaEquipeEstaVerificandoNoMaximoCerca[]{
	all e: Equipe, t: Time |
	lone cercaQueEquipeEstaVerificando[e, t]
}

pred equipeOcupadaQuandoVerificando[]{
	all e: Equipe, t: Time | some  c: Cerca | e in c.disparando.t 
	implies
		situacaoDaEquipe[e,t] = Ocupada
	else
		situacaoDaEquipe[e,t]  = Desocupada
}

fun cercaQueEstaDisparando[c: Cerca, t: Time]: lone Equipe{
	c.disparando.t 
}

fun situacaoDaEquipe[e: Equipe, t: Time]: one StatusDaEquipe{
	e.situacao.t
}

fun cercaQueEquipeEstaVerificando[e: Equipe, t: Time]: lone Cerca{
	e.verificando.t
}

// TESTES

assert testes{
	// só existem 2 bairros
	all s: sistema | #s.bairros = 2
	// há pelo menos uma casa em cada bairro
	all b: bairro | #b.casas >= 1
	// se há ronda em uma casa, também há cerca
	all c: Casa, s: servicos, ce: Cerca, r: Ronda | r in c.s implies ce in c.s
	// se há monitoramento em uma casa, também há cerca
	all c: Casa, s: servicos, ce: Cerca, m: Monitoramento | m in c.s implies ce in c.s
	// se não há cerca em uma casa, também não há ronda
	all c: Casa, s: servicos, ce: Cerca, r: Ronda | ce not in c.s implies r not in c.s
}


pred show[]{}
run show for 20 but exactly 5 Cerca
