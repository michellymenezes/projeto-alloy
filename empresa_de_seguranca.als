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
	all sc: servicoComp | sc in cercaEletrica.servComps
	servicoComp = rondaNoturna + monitoramentoCameras
}

pred show[]{}
run show for 3
