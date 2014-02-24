module bairro

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

fact nomeBairro {
	bairro = autoBranco + centro
}

sig casa{}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{}

sig monitoramentoCameras extends servico{}
