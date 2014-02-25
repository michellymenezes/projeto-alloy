module empresaDeSeguranca

sig bairro{
	casas: some casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	all c: casa | one c.bairro
	bairro = autoBranco + centro
}

sig casa{
	bairro: one bairro
}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{
	r: one cercaEletrica
}

sig monitoramentoCameras extends servico{
	r: one cercaEletrica
}

pred show[]{}
run show for 3
