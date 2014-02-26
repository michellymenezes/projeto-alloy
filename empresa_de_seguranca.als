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
	// cada bairro possui, no mínimo, uma casa
	all a: autoBranco| #a.casas >= 1
	all c: centro| #c.casas >= 1
	// existem dois bairros
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
	// casas possuem ou não algum serviço de segurança
	all c: casa| #c.servicos = 1

	// não existe casa sem bairro
	all c: casa | c in bairro.casas
}

abstract sig servico{}

sig cercaEletrica extends servico{
	camera: lone monitoramentoCameras,
	ronda: lone rondaNoturna
}

sig rondaNoturna{}

sig monitoramentoCameras{}

//FATO SERVIÇO BASICO
fact sobreBasico{
	
	all c: cercaEletrica, c1: casa, c2: casa | cercaPorCasa[c, c1, c2]
	// não existe cerca sem casa
	all s: servico | s in casa.servicos
}

// FATO SERVIÇO COMPOSTO
fact sobreComp{

	one monitoramentoCameras

	// não existe serviço composto sem cerca elétrica
	all r: rondaNoturna | r in cercaEletrica.ronda
	all c: monitoramentoCameras | c in cercaEletrica.camera

}


//PREDICADO

// cada cerca so pertence a uma casa
pred cercaPorCasa[c: cercaEletrica, c1: casa, c2: casa]{
	c1 != c2 => (c in c1.servicos => c !in c2.servicos)
}



pred show[]{}
run show for 10
