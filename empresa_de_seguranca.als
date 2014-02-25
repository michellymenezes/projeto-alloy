module empresaDeSeguranca

sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// FATO DE BAIRRO
fact nomeBairro {
	one sistema
	all a: autoBranco| #a.casas >= 1
	all c: centro| #c.casas >= 1
	all s: sistema | #s.bairros = 2
	one autoBranco
	one centro
	bairro = autoBranco + centro
}

sig casa{
	servicos: lone servico
}

// FATO CASA
fact sobreCasa{
	all c: casa| #c.servicos >= 0

	// não existe casa sem bairro
	all c: casa | c in bairro.casas
}

abstract sig servico{}

abstract sig servicoComp{}

sig cercaEletrica extends servico{
	servComps: lone servicoComp
}

sig rondaNoturna extends servicoComp{}

sig monitoramentoCameras extends servicoComp{}

//FATO SERVIÇO BASICO
fact sobreBasico{
		// não existe cerca sem casa
		all s: servico | s in casa.servicos
}

// FATO SERVIÇO COMPOSTO
fact sobreComp{
	// não existe serviço composto sem cerca elétrica
	all sc: servicoComp | sc in cercaEletrica.servComps

	// todo serviço composto é ronda ou monitoramento
	servicoComp = rondaNoturna + monitoramentoCameras
}


//PREDICADO

// cada cerca so pertence a uma casa
pred cercaPorCasa[s: servico, c1: casa, c2: casa]{
	s in c1.servicos => s !in c2.servicos
}

// cada ronda so pertence a uma cerca
pred rondaPorCerca[r: rondaNoturna, c1: cercaEletrica, c2: cercaEletrica]{
	r in c1.servComps => r !in c2.servComps
}

// cada camera so pertence a uma cerca
pred cameraPorCerca[c: monitoramentoCameras, c1: cercaEletrica, c2: cercaEletrica]{
	c in c1.servComps => c !in c2.servComps
}

pred show[]{}
run show for 10
