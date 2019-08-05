function HTMLEncode ( input )
{
    var converter = document.createElement("DIV");
    converter.innerText = input;
    var output = converter.innerHTML;
    converter = null;
    return output;
}
export default HTMLEncode;