module empresaDeSeguranca

sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set casa
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

sig casa{
	servicos: lone cercaEletrica
}

// ..:: FATO CASA ::..

fact sobreCasa{
	// casas possuem ou não algum serviço de segurança
	all c: casa| #c.servicos >= 0
	all c: casa| #c.servicos <= 1

	// não existe casa sem bairro
	all c: casa | c in bairro.casas
}


sig cercaEletrica{
	camera: lone monitoramentoCameras,
	ronda: lone rondaNoturna,
	status: lone cercaDisparada
}

sig cercaDisparada{}

sig rondaNoturna{
	equipe: set equipeSeguranca
}

sig monitoramentoCameras{}

sig equipeSeguranca{}

// ..:: FATO SERVIÇO::..

fact sobreServico{
	
	// chamando o predicado - cada cerca pertence a uma casa
	all c: cercaEletrica, c1: casa, c2: casa | cercaPorCasa[c, c1, c2]
	// não existe cerca sem casa
	all s: cercaEletrica | s in casa.servicos	
	// só existe uma sala de monitoramento de cameras
	one monitoramentoCameras
	//não existe disparo sem cerca
	all d: cercaDisparada | d in cercaEletrica.status
	// não existe ronda sem cerca elétrica
	all r: rondaNoturna | r in cercaEletrica.ronda
	// não existe monitoramento por camera sem cerca elétrica
	all c: monitoramentoCameras | c in cercaEletrica.camera
	// só existem 3 esquipes de seguranca
	all e: equipeSeguranca| #e = 3
	// chamando predicado - cada cerca possui um diparo próprio
	all d: cercaDisparada, c1: cercaEletrica, c2: cercaEletrica | disparoporCerca[d, c1, c2]
	// cerca possui estado de acionada ou não
	all c: cercaEletrica| #c.status >= 0
	all c: cercaEletrica| #c.status <= 1

}


// ..:: PREDICADOS ::..

// cada cerca so pertence a uma casa
pred cercaPorCasa[c: cercaEletrica, c1: casa, c2: casa]{
	c1 != c2 => (c in c1.servicos => c !in c2.servicos)
}

// cada disparo de cerca so pertence a uma cerca
pred disparoporCerca[d: cercaDisparada, c1: cercaEletrica, c2: cercaEletrica]{
	c1 != c2 => (d in c1.status => d !in c2.status)
}



pred show[]{}
run show for 10
