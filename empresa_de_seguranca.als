module empresaDeSeguranca

sig sistema{
	bairros: set bairro
}

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// Fato sobre bairro
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
	servicos: lone cercaEletrica
}

// fatos sobre casa
fact sobreCasa{
	all c: casa| #c.servicos >= 0
	}

abstract sig servico{}

abstract sig servicoComp{}

sig cercaEletrica extends servico{
	servComps: lone servicoComp
}

sig rondaNoturna extends servicoComp{}

sig monitoramentoCameras extends servicoComp{}

// fatos sobre servico composto
fact sobreComp{
	// não existe serviço composto sem cerca elétrica
	all sc: servicoComp | sc in cercaEletrica.servComps

	// todo serviço composto é ronda ou monitoramento
	servicoComp = rondaNoturna + monitoramentoCameras
}


//PREDICADO

// cada cerca so pertence a uma casa
pred cercaPorCasa[c:cercaEletrica,c1:casa,c2:casa]{
	c in c1.servicos => c !in c2.servicos
}

pred show[]{}
run show for 3
